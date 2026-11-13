# Host families

Libraries hand programs objects of a **tagged family**: one field, the
**tag**, whose value determines the object's shape. Examples are the
TypeScript compiler API's nodes (`kind`), ESTree and Babel nodes (`type`) and
DOM nodes (`nodeType`). The library also exports **guard functions** whose
code is a test of the tag (`ts.isIdentifier`, `t.isIdentifier`).
TScert narrows program-declared discriminated unions by a literal field
([union shapes](UNION-SHAPES.md), R3). A host family is the external case:
the declared type of a family member (`Node`, `Expression`) does not spell
the union of its shapes, and the guards are library code.

This document specifies one mechanism for every such family, parameterized
by a reviewed **family description**. Each part has one implementation,
which reads the description; no part names a family. It states the
description and its activation, then the parts ([tag sets](#tag-sets),
[the family contract](#the-family-contract), [host objects](#host-objects),
[guard recognition](#guard-recognition) and
[stable members](#stable-members)), how family identity follows program
code, the [trust rows](#trust-rows) a family adds, and the instances. The
[compiler API](COMPILER-API.md) is the first instance.

## The family description

A family description is data in the trusted host contracts
(`tools/host-families.mts`, each instance contributed by the contract file of
its package), of one declared type that one interpreter reads, and reviewed
as those contracts are: every entry carries the declaration text it was
reviewed against, and a check compares each with the installed declaration.
It states:

- **package:** the host package's identity, the name and version its
  manifest states;
- **installation:** the audited installation, the package of that name as
  Node's package resolution finds it from a directory of the repository,
  and the digest of its declarations, the SHA-256 of its version and its
  inventory: every `.d.ts`, `.d.mts` and `.d.cts` file under its real
  directory, reached without following a symbolic link, outside a nested
  `node_modules` (the binding check C0 of the
  [compiler API](COMPILER-API.md#binding-the-contract-to-the-implementation),
  of every family). The family's declarations are exactly that inventory,
  by real path: a dependency's declaration and one reached through a link
  are read by the ordinary rules, and a declaration of an arbitrary
  extension (`.d.<ext>.ts`) refuses the installation. The guard table pins
  its executable closure;
- **root:** the root declaration and its form, `inheritance` or `union`;
- **tag:** the tag field $`\tau`$, its primitive, and the source of its
  constants: an enum declaration, which the binding check compares with its
  runtime object, or the string literals the shapes state;
- **table:** an ordered list of selection rules the interpreter applies to
  each tag value, the first that selects a declaration giving $`I_t`$, the
  declaration whose members the tag value's shape reads
  ([the family contract](#the-family-contract)):
  - `literal`: the declaration whose tag is the literal $`t`$, excluding
    declarations that extend another candidate with the same tag;
  - `generic`: the meet of the named generic declarations whose tag
    parameter's bound admits $`t`$, instantiated at $`t`$;
  - `audited`: for a tag value no declaration states as its literal, a
    shape the review states: its bases, declarations of the family, and
    its members, each a property a named declaration states, with the
    text it was reviewed against. Its members are those of an interface
    extending the bases and declaring the members, each read at the
    declaration stating it, and its tag is $`t`$; it is a member of every
    declaration its bases reach, and of no other;
  - `base`: a named declaration;
- **corrections:** the audited members the declarations state required and
  the runtime leaves absent, each read as optional, with its text;
- **omitted members:** the members whose reads give no one value for a
  node's life, each with its text and why: a read that allocates, or a
  member the package assigns on a node it built earlier; each is omitted
  from every shape, so no ordinary read or read link reaches one;
- **footprints:** the methods whose footprint the family's audit states
  (a [statement](SOURCE-ELABORATION.md#stated-effects) it supplies), each
  with its text and its kind: an `empty` method's calls change no location
  of the model, on normal return or throw, and it is read at the empty
  footprint with `onThrow`; a `callbacks` method's own steps change no
  location of the model and the only client code it runs is its
  function-typed arguments, and it is read at each closed footprint
  $`\varepsilon`$, those arguments' types and its call at $`\varepsilon`$,
  on normal return; every other method is read at its declaration;
- **marker:** the value $`m_F`$ of `[[host]]`, the reserved key every host
  object owns ([the host classification](#the-host-classification));
- **stable members:** every property member of a shape, required or
  optional, the tag and the corrected members included, but the listed
  exclusions, with the regression check that reads each twice on a corpus;
- **guards:** the [guard table](#the-guard-table), each entry an export's
  identity and reviewed text, its kind, domain, exact tag set and behaviour
  on `undefined`;
- **undefined inputs:** the guard kinds (node, tag) whose audited behaviour
  on `undefined` the review admits
  ([undefined arguments](#undefined-arguments)); an entry of another kind
  is `unadmitted`.

## Activation

The mechanism is explicit, and nothing activates it by spelling:

- **The family:** a reviewed description in the trusted contracts turns a
  family on, for the installation it names (`reviewedFamilies` in
  `tools/family-activation.mts`). Without one, the package's declarations
  are read by the ordinary rules. Several descriptions are active together,
  each owning its marker and its installation; a declaration is read by the
  description whose installation holds its file, and a run's
  [selection](#the-runs-selection) is one per family.
- **The installation:** Node's `node_modules` lookup
  (`findPackage`, `tools/files.mts`) finds the description's package from the
  description's directory; its manifest states the description's name and
  version, and its declarations have the description's digest, checked once
  per process before any of its declarations is read. Its guard table is
  activated over that installation by the checks
  [below](#activating-a-guard-table).
- **A package's own contract:** the compiler API's tables by name (its
  named views, branded strings, enums read as values, node list and type
  roots, [COMPILER-API.md](COMPILER-API.md#reading-rules)) apply to its own
  installation alone; another family's declarations of those names are read
  as they declare them, under the host reading rules every installation
  shares.
- **The tag enum as a value:** a program reads the description's tag enum
  as a value by the `emitted-enum` rule, where the runtime object the
  activated entry point exports under its name matches its declaration, the
  condition `enumObjectMatches` of [enums](SOURCE-CONTRACTS.md#enums) (C1
  for every family), and where the program's import of it, resolved by Node
  from the importing module and through a program module's re-export as a
  guard's is ([calls](#calls)), binds that very object. Any other enum of a
  family's installation is read as a value only where its package's contract
  lists it, as the compiler API's `hostEnums`, with the same binding
  requirement against the object its contract checks.
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
- A **type stating a program value at a family shape** is refused, since the marker view admits no program object; a forged
  stable view is refused by the decoder; a forged guard call is an ordinary
  call, since recognition is by resolution.
- An **unidentified installation**, whose manifest or declarations' digest
  differs from its description's, or which Node does not find, refuses every
  run reading a declaration of the description's installation, until the
  description is reviewed again (`tests/compiler-api.mts`, and the
  string-tagged family's control in `tests/single-pass-controls.mts`). A guard table that does not
  match its installation leaves the family without guards, each read
  without predicate.

### Activating a guard table

Before a family's [guard table](#the-guard-table) is used, the front end
checks it against the package as Node loads it, once per process, reading the
package's modules with a compiler of its own:

1. **Conditions.** The table's resolution conditions are the ones Node
   enables in the running process, read through a resolve hook, and no flag
   preserves symlinks.
2. **Entry point.** The entry point, by the package's name, resolves through
   Node's own resolver to the recorded module.
3. **The closure on disk.** Before loading the entry point, the front end
   reads and parses its complete executable closure from disk. Every static
   import and export-from, attributes included, resolves from its importing
   module through Node's resolver; an error, a query or a fragment refuses
   the table. The module set, the SHA-256 file digests and the binding edges
   (importing module, local name, target module, exported name, attributes
   and import/export form) equal the table's reviewed closure.
4. **Loading forms.** Dynamic imports, `require`/`createRequire`,
   `import.meta`, `await` and `eval`/`Function` capabilities are outside the
   recorded loading forms and refuse the table. The file digests bind other
   indirect execution to the reviewed code. A refusal at checks 1–4 leaves
   every module of the closure unevaluated.
5. **The loaded functions.** Over the unchanged installation, Node then
   loads the entry point in the front end's own process: each entry's export
   is a function whose text is the entry's, the very function the recorded
   module exports, which declares it with that text and assigns it nowhere.
6. **Their dependencies.** The function's dependency closure, each free name
   a function of its module or a named import without attributes that Node
   resolves from the importing module to a module of the package and that
   the loaded module exports, has exactly the entry's helpers and binding
   edges, each helper of exactly its reviewed text, as loaded where it is
   exported.

A mismatch at any check, or a load Node refuses, leaves the family without
guards, each read without predicate. File digests alone do not pin
resolution, since a manifest or a re-export can select other code among
files already hashed. The checks establish consistency between the reviewed
table and the installation the front end itself runs, under F3.

## The parts of a family

A family is built from the five parts below.

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

- a type the front states at a point (`SourceTypes.translateArm`): its
  labels that are literals of one primitive are one set row;
- a source annotation's lowering (`SourceTypes.numberLabels`) and a
  declaration's equation (`mergeLiterals`, at a union's arms and at the
  literal `0`, whose two zeros are one set);
- a meet row's clauses (`mergeSets`).

Lean's instantiation of an equation at its arguments forms no label, so a
union a substitution forms (`A | 3` at `A = 1 | 2`) stays a union of
labels; the front merges the unions it states, and the element rule
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
lexicographically by Unicode code point: Lean's `String` order and
`codePointLess` in TypeScript, whose own `<` compares UTF-16
code units and would order U+10000 below U+E000.

**Cost.** The demonstrated cost is a residual arm's tag
([residuals](#residuals)): 20 record arms beside one arm whose tag was a
union of 330 literals took 9.2 s through `verify-source.mts` (cbe2893,
2026-10-16). A tag set makes such a union one clause.
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
does ([host classification](#the-host-classification)), so no
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
union (`Identifier | PrivateIdentifier`) is read as declared. Where the
table's `audited` rule gives $`t`$'s shape, $`I_t`$ is the interface that
shape describes, extending its bases and declaring its members, each read at
the declaration stating it: it reaches what its bases reach.

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
never a reserved key but, of a marked shape, `[[viewLength]]`, which the
overlay states of a typed array's view, readonly and stable, its element
count ([reads below the element count](SOURCE-CONTRACTS.md#stated-library-types)). A shape is a definition whose bases are one per
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

A tag set a selected shape's member is read at is selected whole once the
selection meets it: where a member of $`S_t`$, $`t\in K_u`$, has a type
reading a family declaration at a set of literals $`T`$ (`operatorToken:
BinaryOperatorToken`, `Token<BinaryOperator>`) and $`T\cap K_u\neq\varnothing`$,
$`T\subseteq K_u`$, closed over the members of the shapes it adds. A type
read at $`T`$ is then within the arms of $`K_u`$ rather than across an arm
and $`R_u`$. The formula above holds of this $`K_u`$ as of any selection,
so the reading's meaning, and its trust, are those of any selection.

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
[qualified import](SOURCE-CONTRACTS.md#certified-imports) requires; with
different selections their residuals would differ in meaning, not only in
form. A run's own selection is a fact of the front end, so no checker
premise states it.

#### Agreement across runs

Two runs read one family type with different arms, whose record meanings
differ: $`R_u`$ admits objects with the marker and only the common members.
A value a unit of one run passes a unit verified in another at a family
type is read by both through their own arms. That the two readings agree on the values that occur is a
correspondence between the units' sources and the host's objects (F1′): a
marked value with the tag $`t`$ meets $`S_t`$. It is an external obligation
of the import rule's assumption that a separately verified function meets
its importer's reading. It is no premise of any checker proof, no conjunct of
`WorldAdm`, and no subtyping between the units' residuals;
`mode8Accepted_sound` keeps its statement.

### Host objects

A host package's objects reach the program only from the package. The
model classifies them, so that no step exposes their own keys and no program
object passes for one. The compiler API's nodes and node lists are the
examples; its trust rows ([T1–T8](COMPILER-API.md#trust)) are the
assumptions the statements below are relative to.

#### Restricted values

A **restricted value** is a host value: an object the package creates whose
prototype chain carries the prototype of a package class (a node, a type, a
symbol, a checker, an `API`), or a node list. Neither is callable. The
package's classes, as constructors, are admitted only as the callee of `new`
and as the receiver of a direct call of a static member; its exported
functions are ordinary function objects (T4) of their declared function
types. The model reads a host object as a record whose stated members are
readonly views
([stable members as readonly views](COMPILER-API.md#stable-members-as-readonly-views)),
and a node list as a dense readonly array of its elements
([node lists](COMPILER-API.md#node-lists)),
each interpreted by the existing record and array semantics. The runtime
objects are not those: a node's stable members are getters on its
prototype, a node list's indices are getters, and the own enumerable keys
of both are the class's data fields (`parent`, `view`, `index`,
`_byteIndex`; for a list `parent`, `view`, `sourceFile`, `_cursorIndex`,
…). Under Node, `{ ...node }` has `parent` and no `kind`
(`tests/compiler-api.mts`). The reading is faithful for the operations T4
states, and the operations whose model would not hold of a restricted value
are stuck on one and carry an obligation excluding it.

#### The host classification

Every object of the model carries a classification, **host** or
**ordinary**, in its field map, which maps each own key to a location and is
fixed with the object as its call code is: a host object owns the model's
reserved key `[[host]]`, which no source key spells. The classification is
fixed when the object is allocated, or, for an object of the external heap,
when it first enters the world, and never changed. World extension (`Adm.mono`) and
truncation to a lower step index (`Adm.down`) keep every value, so they keep
every classification. Exactly the package's instances and its node lists
are host; no step of the calculus allocates one, and a host entry's result
reveals the classification of the object it gives and changes none. The
model value of a host object keeps own fields and inherited lookup
separate, as the calculus's prototype-chain lookup does: it owns its stated
members, holding their values, and the runtime object's undeclared own
data fields (`parent`, `view`, `_cursorIndex`, …), whose contents the model
leaves unknown; its prototype field leads to model prototype objects owning
the keys its runtime chain provides beyond its own (a node list's `at`,
`pos`, `forEachNode`, then `Array.prototype`'s). A node list's own keys are
its store of the $`v_i`$, `length` and those data fields, none of them a key
its prototypes provide (T4).

The families of the types a host value can be held at admit host objects:
readonly views (`viewT`), optional members (`optT`), methods, readonly
arrays and tuples, `unknown`. The families that grant a capability over an
object's own keys admit ordinary objects only, and so does every family of
a callable or a primitive:

- a record with an invariant field (`refsT` of a non-empty field list), and
  a writable array or tuple, whose store is an invariant field;
- a record whose own-key bound does not admit `[[host]]` (`ownKeysT`, a
  bound listing keys without it or excluding it), and a dictionary
  (`dictViewT`, `dictCellT`);
- a call or construct signature, whose objects carry code.

The steps that copy, write or expose the values of an object's own keys
(an object's merge, which a spread, an object pattern's rest and
`Object.assign` lower to; `Object.assign`'s copy onto its target; and the
parameter of `Object.values`, `Object.entries` and
`Object.getOwnPropertyDescriptor`, stated at the non-host values) are
stuck on a host object. So the
safety of an accepted program gives every operand of these steps ordinary:
capability preservation is type soundness over the classified families,
proved with it, relative to the host entry contracts (T1, T3, T6) and to code
outside the certified units (T8).

#### Excluding host values

The checker's rule for each stuck step requires
$`\mathrm{excludesHost}(A)`$ of the operand's claimed type $`A`$, a
predicate on its clauses whose soundness, $`v\in⟦A⟧`$ giving $`v`$
ordinary, is proved clause by clause from the families above. A clause
excludes host values when it is a primitive or a singleton of one, a call or
construct signature, a record with an invariant field, a record with an
own-key bound that does not admit `[[host]]`, a dictionary, or a writable
array or tuple. A union excludes host values when every arm does, and an
intersection when one conjunct does. A type parameter excludes them when
its certified bound does, since an admissible instance's values lie in the
bound's meaning; an occurrence of the parameter inside its own bound counts
as not excluding, so a recursive bound is decided in one pass,
conservatively. A type reference is decided by its definition, a reference
met again on the same path counting as not excluding. `unknown`, `object`,
a readonly array or tuple, and a record of readonly or optional fields
alone exclude nothing, and nor does a union with such an arm
(`invalid-spread-empty-record`, `invalid-reflect-own-keys-object`,
`invalid-spread-readonly-array`, `spread-readonly-record-refused`).

Records are open: a record type constrains the fields it names, and a value
of it may own others. So no operation traversing every own key is admitted,
with one exception: `JSON.stringify` takes `JsonValue`
(`library-globals.mts`), whose object arms are a string-indexed dictionary
of `JsonValue` and a readonly array of `JsonValue | undefined`.
Serialization enumerates the own keys of an object that is no array
(SerializeJSONObject) and reads an array only at `length` and its indices
(SerializeJSONArray). The claim: in a world satisfied by the heap, the
traversal of a `JsonValue` within step index $`k`$ enumerates the keys of
no host object.

For the primitive and dictionary arms it is proved: for every family whose
members are non-objects or dictionaries of string keys at the family itself,
the string-key traversal reaches no host object
(`JsonTraversal.reach_noHost`), and a type is such a family when each of its
clauses is a primitive one or a dictionary indexed by every string key at the
type (`shaped_of_clauses`). The statement is safety within the index, not
termination: a cyclic heap is traversed as deep as the index allows. Each
object it reaches meets the dictionary arm, whose objects are ordinary and
have no model prototype ($`\mathrm{dictViewT}`$); each value under a string
key meets $`\mathrm{dictViewT}`$'s index contract, a `JsonValue` at every
lower index, so the argument descends by induction on the index, the heap's
satisfaction of the world giving each location's value its contract.
`toJSON` is a string key, so it holds a `JsonValue`, never a callable.
Symbol-keyed fields, which the dictionary does not constrain and which may
hold a host object, are ignored by serialisation.

For the array arm it is argued here; `reach_noHost` does not state it, since
its premise admits no array. A member of the array arm owns the store key,
so it is a JavaScript array (the trust surface, DESIGN.md), and
serialization reads it by its indices only: it may be a host object
(readonly arrays admit them), and its other own keys are not read. It owns
no `toJSON` (the array clause's own-key exclusion) and inherits none (the
trust surface). Each index read gives an element of its store, a
`JsonValue | undefined` at a lower index by the store's element contract,
or, at a hole, `undefined`, since neither `Array.prototype` nor
`Object.prototype` owns a numeric key; SerializeJSONArray writes `null` for
`undefined`. So the traversal continues at a `JsonValue`, and the descent
proceeds by induction on the index as for the dictionary arm.

#### Operations and their obligations

Each source form the fragment admits and each entry of the reviewed library
overlays (`library-globals.mts`, `array-prototype.mts`) has one
classification: **transparent**, its model holding of a restricted value as
of any value of its operand's type (a callback the operation calls keeps its
own callable contract and effect); **obligated**, a step stuck on a host
object, or a library parameter stated at the non-host values, whose rule
requires $`\mathrm{excludesHost}`$ of its operands; or
refused, a form the fragment does not admit. A library entry's model is its
reviewed contract (a result type and an effect), so an entry whose contract
holds of every value of its parameter types, host objects among them, is
transparent although the runtime answer depends on own keys: `Object.keys`
of a node is a fresh array of strings, which is all its contract states.
The obligated forms are those whose model result states the operand's
members as own keys, and those that hand the values of a host object's own
fields to the program: those fields hold the package's mutable internal
heap (a list's `_cursorIndex`, which an indexed read changes; its
`sourceFile`, whose `nodes` cache grows as nodes materialise), which the
model does not describe, and an `unknown` result does not stop its later
refinement and reflection.

The classifications are recorded in `host-operations.mts` and in each
overlay entry's required `host` field (`library-globals.mts`). The tables
of source forms are keyed by the parser's unions of expression, statement
and pattern kinds, so a form added to the fragment is a type error there
until it is classified; the table of intrinsics is keyed by name, and its
completeness against `intrinsics.mts` is reviewed, not checked. No check
reads the classifications: they are the reviewed record, and Lean enforces
each obligated step by its own rule.

| Operation                                                                                                                      | Model                                                                                  | Classification                                                                  |
| ------------------------------------------------------------------------------------------------------------------------------ | -------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------- |
| a member read in every form (`o.m`, `o?.m`, `o["m"]`, a pattern's key); a call of a stated method                              | the member's value                                                                     | transparent                                                                     |
| `===`, `!==`, `typeof`, `Array.isArray`, `"k" in o`, `%HasProperty%`, `instanceof` a class of the file                          | identity, type tag, the store, the model value's keys                                  | transparent; `in` narrows nothing                                               |
| `for…of`, `[...x]`, `f(...x)`, `const [a, ...r] = x`, `[a, ...r] = x`                                                          | the store's elements                                                                   | transparent (a node list's table)                                               |
| `f.apply(t, x)`, `f.call(t, …)`, `f.bind(t, …)` of a client function                                                          | `x`'s `length` and indices                                                             | transparent                                                                     |
| `new Set(x)`; `new Map(x)` with `x` an array of pairs; either of a host collection                                             | the store's elements; a pair's `0` and `1`; the collection's                           | transparent; a node list is no array of pairs and no host collection            |
| `Promise.all(x)`                                                                                                               | elements at `Promise` types                                                            | transparent: realm promises by the [await assumption](SOURCE-CONTRACTS.md#async-functions-and-await), never host objects |
| `String(x)`, a template, `+` with a string, `join`, `toString`                                                                 | the complete [conversion contract](SOURCE-CONTRACTS.md#prototype-contracts)            | transparent where the operand meets the complete contract: a node list owns no `toString`, `join` or `Symbol.toPrimitive`, its prototypes provide none but `Array.prototype`'s, and its elements, nodes, meet the contract nowhere, so only an empty list can |
| every member of the array overlay on a readonly receiver, `at` included                                                        | its contract                                                                           | transparent: a node list inherits each but `at`, whose override gives `undefined` where `Array.prototype.at` gives an element, within the contract `T \| undefined` |
| `Object.keys`, `for…in` (`%ForIn%`)                                                                                            | a fresh array of strings; strings                                                      | transparent                                                                     |
| an [open read](SOURCE-CONTRACTS.md#open-reads) `o.k` (`%Read:k%`) of an object TypeScript types by `in` tests alone          | the value the lookup finds, at `unknown`                                               | transparent by the open-read restriction; a receiver a family's type describes states its keys, and a key it does not state is an open read only at an audited key, in a read an `in` test makes eligible |
| `Object.values`, `Object.entries` at `{}`, `Object.getOwnPropertyDescriptor`                                                   | the values of the operand's own fields                                                 | obligated: $`\mathrm{excludesHost}`$ of the operand                             |
| `Object.getOwnPropertyDescriptor(o, k)?.value` read only as a string (`%OwnString%`)                                         | the string `o` owns at `k` as a data property, else `undefined`                        | transparent: [[GetOwnProperty]] runs no code, and only a string reaches the program ([`Object` and `Reflect`](SOURCE-CONTRACTS.md#object-and-reflect)) |
| `Object.values` and `Object.entries` at a dictionary, `%Iterate:ForIn%`                                                        | the dictionary's values                                                                | transparent; the parameter excludes host values                                 |
| `JSON.stringify(x)`                                                                                                            | a string                                                                               | `x` at `JsonValue`                                                              |
| a `console` method                                                                                                             | nothing observed                                                                       | every argument's type a primitive or a union of primitives                      |
| an object spread, an object pattern's rest                                                                                     | a fresh record of the operand's members                                                | obligated: $`\mathrm{excludesHost}`$ of the operand                             |
| `Object.assign(t, s…)`                                                                                                         | `t` with each `s`'s members                                                            | obligated: $`\mathrm{excludesHost}`$ of `t` and of each `s`                     |
| a member write                                                                                                                 | the receiver's invariant field written                                                 | the write rule's invariant field, which excludes host values (R1)               |
| `Object.hasOwn(o, k)`                                                                                                           | a Boolean                                                                              | transparent: [[GetOwnProperty]] runs no code, and no value of `o` reaches the program |
| `Object.freeze` of an object literal written as its argument (`%Freeze:K%`)                                                   | the fresh object, its fields readonly views                                            | transparent: a fresh object, no host value                                      |
| `Array.from` of an array or of a length record; `structuredClone(x)`                                                                               | the store's elements; a value at `unknown`                                             | transparent                                                                     |
| `Object.getPrototypeOf(o)` compared with `Object.prototype` (`%PrototypeIs:Object%`), `Reflect.ownKeys(o)` (`%OwnKeys%`)        | `o`'s [[GetPrototypeOf]]; its [[OwnPropertyKeys]]                                     | obligated: $`\mathrm{excludesHost}`$ of `o`, whose internal methods may be the host's code |
| `concat` of arrays, `hasOwnProperty`, `delete`, `Object.freeze` of any other operand, other prototype reflection                | —                                                                                      | refused: not in the fragment                                                    |
| `sort`, `reverse`, `push`, `pop`, `shift`, `unshift`, `splice`                                                                 | the receiver's store written                                                           | a writable receiver, which excludes host values                                 |
| an `Array.prototype` member called with another receiver (`Array.prototype.sort.call(l)`)                                      | —                                                                                      | refused: no library value but `Boolean`, `String` and `Number` is admitted as a value                  |

**First-class library values.** The obligated library calls are members of
`Object`: `Object.assign`, a call form of the parser recognized by its
binding, and `Object.values`, `Object.entries` and
`Object.getOwnPropertyDescriptor`, entries without `value`. `Object` is
admitted as no value, so no alias (`const values = Object.values`),
extraction (`const { assign } = Object`) or argument
(`consume(Object.entries)`) reaches one. A library global is read as a value
only where its entry says so (`value`: `Boolean` alone), and only a
transparent entry may.

#### Host objects in Lean

The host classification is the reserved key `[[host]]` (`hostKey`) of an
object's field map, beside the model's `[[proto]]`, `[]` and `[[code]]`. No
source key spells it, since the model spells a JavaScript string key apart
from its own keys (`escapeKey`), so neither a written key, a computed one
nor `in` reaches it; no certified allocation makes one, since the literal
rules exclude the key (`HasTyWith.alloc`, `allocDict`), a merge copies no
model key (`copiedKey`, `mergeParts_host`) and a computed key is never one
(`Unreserved`). The families listed above admit it or not as stated
(`refsT` of a non-empty field list, `dictViewT`, `dictCellT`, an own-key
bound without the key, `NoHost`), the merge step, which `Object.assign`
lowers to, is stuck on it (`ownAll`, `ownData`) and its rule requires
`hostFree` of every operand clause (`MergeOk`, `hostFree_sound`). The
family of non-host values is the type term `nonHost`, which only the library
overlay states, lowered to the primitives, the callables and the record
clause whose own-key bound excludes `[[host]]`; a source record clause meets
that bound when it names an invariant field or an index (`CoversBounds`,
`refs_noHost`, `dict_noHost`), and the stated parameter of the
obligated `Object` members is the family of **non-host values**: the
primitives, the callables and the ordinary-classified objects. The
checker's admission rule for an argument at that parameter is
$`\mathrm{excludesHost}`$ of the argument's claimed type, and the lemma
proved for it is semantic inclusion: $`\mathrm{excludesHost}(A)`$ gives
$`⟦A⟧\subseteq`$ the non-host values. The family is no structural type
(an empty object type would admit host objects), and subtyping into it is
this rule alone. A type parameter is included only through its certified
bound; an unconstrained parameter and a recursive occurrence in its own
bound supply nothing; a union needs every arm and an intersection one
conjunct. The
checker's rules for those steps and parameters require
$`\mathrm{excludesHost}`$ of the operands' claimed types, proved sound
against the families. An operation without a certified rule fails
its plan's certification, so no recognizer's completeness is assumed. The
headline theorem is `SourceClaimJson.PassUnit.mode8Accepted_sound`, its
premise `Mode8Accepted f i`, the verifier's mode 8 acceptance of unit
$`i`$'s group over the file's plans $`f`$; its conclusion `PassUnitSafe f i`,
over the classified semantics, gives every member of the group, at every
admitted assignment of its type parameters and from every entry meeting
its inputs, safety, so no stuck step, so no host object at an obligated operand,
including the steps a native entry runs on its behalf (a callback's). Certified
operations use the array and record rules, and their agreement with the
runtime objects is T4.

The policy refuses some ordinary programs: a spread or an object rest of a
readonly record that holds no host value, `Object.assign`, `Object.values`
or `Object.entries` of one, `console.log` of an object, `structuredClone` of any value. Each refusal is
a coverage loss, recorded as such.

### Guard recognition

A guard of a family is read from an audited table of what its code does,
never from its name or its declared predicate. A declaration such as
`isTypeAliasDeclaration(node: Node): node is TypeAliasDeclaration` is the
package author's statement, and it is false: the function also accepts
`JSTypeAliasDeclaration`, a JSDoc `@typedef`, whose kind is 345 where
`TypeAliasDeclaration`'s is 266. Read at that predicate, as an imported
guard's declared type is
([user-defined guards](SOURCE-ELABORATION.md#user-defined-guards)), the program
`isTypeAliasDeclaration(n) ? n.kind : undefined` typed
`SyntaxKind.TypeAliasDeclaration | undefined` verifies and returns 345 under
Node. No guard of a family is read at its declared predicate: a guard the
table lists narrows by its entry, and every other is read at its declared
parameters and result without predicate, narrowing nothing. So is every
other function of the host package declaring a predicate, the sync API's
`isIntrinsicType(type: Type)` among them (`invalid-compiler-api-sync-guard`):
a predicate of the package narrows only by an audited entry, a guard table's
or a [stated type guard](COMPILER-API.md#stated-type-guards)'s.

It is an instance of the effects vision: an operation
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
  guard returns `true`, for every member of the domain;
- its **behaviour on `undefined`** $`u_g`$, outside the domain: `throws`, a
  `TypeError` thrown before any other step; `false`, the answer `false`
  with no other step; or `unadmitted`, an argument the domain obligation
  refuses ([undefined arguments](#undefined-arguments)).

The entry states that, for every argument in its domain, the guard
returns `true` exactly when the argument's tag (a tag guard: the argument)
is in $`K_g`$, reads nothing of its argument but the tag, runs no other
code, throws nothing, and returns the same answer whatever it receives
beyond its one parameter (further arguments, a receiver); and that on
`undefined` it behaves as $`u_g`$ states, whatever else it receives.

[Activation](#activating-a-guard-table) checks each entry against the
package as Node loads it before the table is used; a mismatch leaves the
family without guards. An entry's statement rests on F3 and F5 of the
[trust rows](#trust-rows).

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
- the body declares nothing but $`y`$ and assigns nothing;
- each comparison has a constant on one side and $`e`$ on the other, each
  helper's argument, $`y`$'s initializer and a `switch`'s subject is an
  $`e`$, parentheses aside, and no member read or call is an optional
  chain.

The generator (`dev/guard-table.mts`) reads a description's entry point, tag
field and tag enum, and computes $`K_g`$ by evaluating $`c`$ over
$`\mathcal T_F`$, the values of the enum the entry point exports as Node
loads it. A function outside the contract, or one whose bindings do not
resolve, gets no entry: it loses its predicate and any preservation effect.
The generator's output is compared with each family's reviewed table in a
fast check (`tests/compiler-api-guards.mts`),
and a Node run of every entry on an object of each tag compares its answers
with $`K_g`$, and a run on `undefined` of each entry whose $`u_g`$ is
`throws` or `false`, with further arguments and a receiver and without,
with $`u_g`$; both are regression evidence for the
review, not proofs of the entry's statement.

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
of the package in a nested `node_modules` (the nested-installations
control in `tests/single-pass-controls.mts`). The
fixture projects resolve the package as Node does, through installation
links (`pipeline/fixture-links.mts`), with no `paths` for it. A
same-named local function, a re-bound name, or a function wrapping a guard
is an ordinary call, the wrapper an ordinary verified function. The
declaration TypeScript binds, the family of its parameter's type (or its
tag enum's) and the function Node binds are one description's: a guard Node
binds to another family's function of the same name and domain is an
ordinary call (the string-tagged family's control in `tests/single-pass-controls.mts`). A call with
a spread or more than one argument is refused.

**A call on an immutable name** $`x`$, a binding no write in its scope
names ([written](SOURCE-ELABORATION.md#a-let-nothing-assigns), `unassigned`:
a nested closure's write counts, another binding's of the same name does
not), read where it is initialized (`readScope`, which stops at
the read's nearest binding of the name: a parameter after its own
declaration, a block's or a `switch` clause's `const` or `let` initialized
at every read, a loop's binding in the loop's body and, for a `for` loop,
its test and update, a `catch` clause's binding in its block), is written
as the Fragment's membership test, `tagMember`, of
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
`tagMember`, checking $`x`$'s type at $`P`$, the family type with its
marker, whatever type the walk computes for $`x`$; a value the checker cannot type there
(an `unknown`, `null`, an arbitrary object) refuses the call, located at the
call. Where $`u_g`$ is `throws` or `false`, the obligation is of the
argument's value other than `undefined` ([undefined arguments](#undefined-arguments)). The Fragment decoder refuses a `tagMember` without its domain, an
empty $`K_g`$ included.

**A call on any other argument** (a call's result, a member path) is an
ordinary call of the guard at the signature its entry gives
(`guard-value`, below): the call evaluates the argument once and
propagates its exception, Lean's call rule checks the argument at the
domain, and the promise narrows no binding, since no name holds the
argument. A member path narrows with [stable members](#stable-members).

On the guard's admitted domain the test is exactly the guard: `true` on an
argument whose tag is in $`K_g`$, `false` otherwise, by the entry. The
`false` edge subtracts $`K_g`$ from what $`x`$ already holds
([member-split](PROGRAM-TYPING.md#a-membership-test)): an arm of the object
whose tag is one of the set's tags, or a set of tags all in $`K_g`$, is
dropped (a `Token` arm of its tag set, under `isToken`'s `false`); an arm
whose tag set is partly in $`K_g`$ is read at the rest of its set, an
application of its generic declaration at those tags, where its tag is a
stable member, and is kept whole otherwise (`compiler-api-guard-false-sets`,
`compiler-api-guard-false-branch`, `compiler-api-guards`).

A tag guard's call on an immutable name $`x`$ is the membership test of
$`x`$ itself, $`\mathsf{member}(K_g, x)`$, with $`P`$ the tag's primitive,
and refines $`x`$ on both edges (`isModifierKind(kind)`); a broad number
stays a number on the `false` edge. On any other argument it is an ordinary
call at `tag-guard-value`.

#### Undefined arguments

A guard's behaviour on `undefined` is part of its entry, $`u_g`$, so a call
on a value that may be `undefined` (`ts.isIdentifier(n.parent)`, whose
`parent` a correction reads optional) is the guard's own behaviour there,
then its test on the rest. With $`s : A`$ the argument's slot, and
$`A_{\mathtt{u}}`$ and $`A_{\lnot\mathtt{u}}`$ the slices of $`A`$ where the
value is and is not `undefined` ($`\mathsf{tagSlice}_G(A,\mathsf{isUndef},\cdot)`$):

```math
\frac{g\ \text{an entry of}\ F,\quad u_g\in\{\mathsf{throws},\mathsf{false}\},\quad K_g,\quad \Gamma\vdash s : A,\quad A_{\mathtt{u}}\neq\emptyset}
     {g(s)\ \leadsto\ \mathsf{tagBind}\ \mathsf{isUndef}(s):\ \mathsf{true}\mapsto r_g,\ \ \mathsf{false}\mapsto s : P\ \text{checked};\ \mathsf{member}(K_g,\ s.\tau)}\ \textsf{host-guard-undefined}
```

with $`r_g`$ the throw of a fresh `TypeError` where $`u_g = \mathsf{throws}`$,
the error the calculus's abstraction of one, a fresh object owning no key,
as at [a member of `null` or `undefined`](PROGRAM-TYPING.md#members-of-primitives-and-nullish-values),
and `false` where $`u_g = \mathsf{false}`$. The domain obligation and the
membership test are `host-guard-operand`'s, at $`A_{\lnot\mathtt{u}}`$.
Where $`A`$ has no `undefined` slice, or $`u_g = \mathsf{unadmitted}`$, the
call is `host-guard-operand`'s, so an `undefined` argument of an
unadmitted entry fails the obligation. The edges refine $`s`$
([member-yield](PROGRAM-TYPING.md#a-membership-test)) to

```math
\begin{aligned}
\mathtt{true}&:\ \mathsf{slice}_{\mathsf{true}}(A_{\lnot\mathtt{u}})\\
\mathtt{false}&:\ \mathsf{slice}_{\mathsf{false}}(A_{\lnot\mathtt{u}})\ \ \text{where}\ u_g=\mathsf{throws},\qquad \mathsf{slice}_{\mathsf{false}}(A_{\lnot\mathtt{u}})\cup A_{\mathtt{u}}\ \ \text{where}\ u_g=\mathsf{false}
\end{aligned}
```

so a guard's `true` holds of a present value, and a throwing guard's normal
return holds of one on both edges. A handler of the throw receives the
heap of the call and no refinement of $`s`$. The rule is a lowering, no
typing rule: Lean writes the call (`LoweringAtoms.memberAt` for a test of a
slot, `closureExpr`'s `tagMember` case for an operand) as the dispatch, the
fresh error and its throw (`raiseTypeError`) or `false`, and the
membership test, each node certified by the calculus's existing rules, and
checks each edge's context as every edge's.

**The audit.** $`u_g`$ is the generator's proposal (`dev/guard-table.mts`),
which the review authorizes. The generator evaluates the accepted body on
`undefined` through the recognition grammar, as it evaluates it on each tag
value, with JavaScript's semantics of each form: $`x`$ is `undefined`, the
read $`x.\tau`$ of it throws a `TypeError`, a constant is its value, `===`
and the ranges compare as JavaScript compares (`undefined` equals no
constant and is in no range), `||` and `&&` evaluate their right operand
only where JavaScript does, and a helper's call evaluates its argument,
then the helper's body on it. Every step of the grammar but that read has
no effect. So:

- where the evaluation reads $`x.\tau`$, it throws there before any step
  with an effect, and $`u_g`$ is `throws`: every node guard whose body
  reads its tag before any other test (`return x.τ === κ`, `const y = x.τ;
  …`, `switch (x.τ)`, `return h(x.τ)`, `return h(x)` of such an $`h`$);
- where it answers `false`, it ran no other step, and $`u_g`$ is `false`:
  a public tag guard, whose equalities compare its argument with constants;
- otherwise, and for a kind the description's undefined inputs do not
  list, $`u_g`$ is `unadmitted`.

The grammar compares the argument's tag, or a local holding it, or the
argument, with a constant, one on each side of a comparison, calls a helper
on the argument or its tag, and reads no optional chain; the generator
refuses any other comparison (`x === x`, `κ === κ`, also parenthesized), a
helper's call on a constant, a local holding a constant, and `x?.τ`, each
of which can answer `true` of `undefined` and of a value of the primitive
no tag is, or reach the tag read after a step the grammar does not have
(the stand-in's `isSameType`, `isConstantType`, `isParenthesizedType`,
`isNameOfConstant`, `isCallAfterConstant`, `isNameOptional`, each without
entry).

A function answering `true` on `undefined` (`x === undefined || x.τ ===
κ`) reads $`x`$ beyond its tag, so it is outside the recognition contract
and has no entry. The audit is of `undefined` alone: `null` and every other
value outside the domain keep the obligation. Its result:

| Family | Kind | Entries | $`u_g`$ |
| --- | --- | ---: | --- |
| compiler API | node guard | 308 | `throws` |
| compiler API | tag guard | 29 | `unadmitted`; tag guards are not among the description's undefined inputs (each answers `false` under Node) |
| stand-in | node guard (`isName`, `isExpression`) | 2 | `throws` |
| stand-in | tag guard (`isNameType`) | 1 | `false` |

C2's Node run of every entry whose $`u_g`$ is `throws` or `false` on
`undefined`, with further arguments and a receiver and without, compares
its behaviour with $`u_g`$, for both families; an `unadmitted` entry states
no behaviour there and is not run on it, and a description forged to state another behaviour fails it
(`tests/compiler-api-guards.mts`). The behaviour rests on F3 of the
[trust rows](#trust-rows), which states it of the same resolved functions
as the rest of the entry; it adds no trust row. Cases:
`compiler-api-guard-undefined` (a loop up `parent`, a path under `&&`, a
local, the `false` edge, a caught throw, the argument evaluated once, a
callback); `invalid-compiler-api-guard-undefined-object` (a program object
of a parenthesized expression's kind, which the guard answers `true` of
under Node, refused at the domain obligation);
`invalid-compiler-api-guard-undefined-user` (a user guard's `true` on
`undefined` keeps it); `invalid-compiler-api-guard-undefined-catch` (a
handler's `parent` may be absent); `invalid-compiler-api-guard-undefined-tag`
(a compiler-API tag guard's argument that may be `undefined`, refused at
the domain obligation). A document stating every call's behaviour
`unadmitted` refuses every unit reading through such a guard
("forged fragment: a guard's undefined behaviour" in `tests/single-pass-controls.mts`).

#### Guards as values

A listed guard **used as a value** (`statements.filter(ts.isImportDeclaration)`,
a guard passed to a function) is read at the signature its entry gives, in
place of its declared type. A node guard:

```math
\frac{g\ \text{a node guard of}\ F,\quad K_g,\quad A\ \text{the reading of its domain}}
     {g : (A)\to\mathtt{boolean}\ \{\mathsf{keep},\mathsf{keep}\}\ \land\ (A)\to\textstyle\bigcup_{t\in K_g} S_t\,[\mathsf{guards}\ 0]\ \land\ (A,\ \ldots\mathtt{unknown}[])\to\mathtt{boolean}\ \{\mathsf{keep},\mathsf{keep}\}\ \land\ (A,\ \ldots\mathtt{unknown}[])\to\textstyle\bigcup_{t\in K_g} S_t\,[\mathsf{guards}\ 0]}\ \textsf{guard-value}
```

A tag guard promises a union of literals, its domain the tag's primitive
$`P`$:

```math
\frac{g\ \text{a tag guard of}\ F,\quad K_g}
     {g : (P)\to\mathtt{boolean}\ \{\mathsf{keep},\mathsf{keep}\}\ \land\ (P)\to\textstyle\bigcup_{t\in K_g}\{t\}\,[\mathsf{guards}\ 0]\ \land\ (P,\ \ldots\mathtt{unknown}[])\to\mathtt{boolean}\ \{\mathsf{keep},\mathsf{keep}\}\ \land\ (P,\ \ldots\mathtt{unknown}[])\to\textstyle\bigcup_{t\in K_g}\{t\}\,[\mathsf{guards}\ 0]}\ \textsf{tag-guard-value}
```

with $`\{\mathsf{keep},\mathsf{keep}\}`$ the footprint that changes no value
and no store, $`\bigcup_{t\in K_g} S_t`$ the union of the root's arms under
the run's selection whose tags meet $`K_g`$ (the family's definition
`guard.g`, of one arm per tag of $`K_g`$ where the selection gives each its
own, an arm covering several tags otherwise), and the promise signature of
[user-defined guards](SOURCE-ELABORATION.md#user-defined-guards), which
narrows the `true` edge. The parameter is the domain: a callback receives
the guard only where its argument type is within $`A`$ (or $`P`$), so its
marker is established at every call; the entry states that further
arguments (an index, the array) and a receiver change no answer, which the
third and fourth signatures state, so the guard meets a callback of more
parameters, the fourth one promising (`nodes.filter(ts.isIdentifier)` holds
identifiers, `compiler-api-guard-values`,
`blocker-compiler-api-filter-guard-element`). The
declaration document states this signature for the guard's import, so Lean
reads it as any import's declared type; what it rests on is the table.

The run's [selection](#the-runs-selection) includes $`K_g`$ for every
listed node guard its candidate modules call or use as a value, so the
shapes a guard tests are arms of the union it narrows.

### Stable members

A test refines the slot holding the value it tests, and the narrowing rules
([guards](SOURCE-ELABORATION.md#guards)) refine every slot known to hold that
value. A **path** $`p = x.f_1\cdots f_n`$, $`n\ge 0`$, is a root binding
$`x`$ held in the activation's environment and member reads: an immutable
binding, or a `let` or assigned parameter held in a slot
([paths rooted at a slot](#paths-rooted-at-a-slot)). Each evaluation of a path reads it anew:
`ts.isIdentifier(m.name) && m.name.text` reads `m.name` twice, into two
slots. Path refinement is the knowledge that a later read of a path gives
the value an earlier read gave, so that it sees the earlier read's
refinement. It has two parts: linked reads, which hold of every admitted
object until a call or a write, and stable links, which hold of the members
whose locations have stable contracts through every step; a family's stable
members are the ones introduced at such locations, by F2.

The refinement is a type of the slot, never of the root. A view's contract
implication ranges over every world at a lower level (`viewT`), and the
slice a test leaves of the current value holds at the current world alone,
so no refined view of the root follows from it.

#### Linked reads

A read $`r\leftarrow x.f`$ records the read link $`x.f\mapsto r`$: the
object in $`x`$ holds $`\rho(r)`$ at its field $`f`$ in the current heap
(`readFrame`, [checked expression postconditions](PROGRAM-TYPING.md#checked-expression-postconditions)).
A later read of $`x.f`$ where the link holds gives that value:

```math
\frac{x.f\mapsto y\in\Sigma\quad \Gamma\vdash y : B\quad B\le A}
     {\Gamma;\Pi;\Sigma\vdash_G r\leftarrow \mathsf{readAt}\,f\,x : A\dashv\Pi,\ r=y;\ \Sigma}\ \textsf{read-linked}
```

The read is a step of the program, as any read; the rule types its result.
It is sound because $`\Sigma`$ holds of the current heap, so the read returns
$`\rho(y)`$, and $`\Gamma`$'s types hold of the environment at the current
world. A link through a key the object may lack (an optional link) covers
the absent key's `undefined` as well. The rule holds of every admitted
object, program records and host values alike, because a read of a member is
a read of a data property: the source fragment admits no accessor in a
program object ([source boundary](SOURCE-FRAGMENT.md)), a structural input is
a plain data object by the caller contract
([trust surface](DESIGN.md#trust-surface)), and a host value's reads are its
model's by its audited correspondence (T4). An object outside these, one
whose getter answers differently on two reads, is outside the caller
contract; a boundary control runs it under Node. Its invalidation is the read
link's: a write discards read links, a call discards them, and a closure's
entry states none.

Paths compose through equalities: a read of `x.f.g` reads `x.f`, which the
link $`x.f\mapsto y`$ gives as $`y`$, and then `g` of it, which a link
$`y.g\mapsto z`$ gives as $`z`$. Two evaluations of one path under live links
are one value, so two tests of it refine one slot:
`(ts.isIdentifier(m.name) || ts.isPrivateIdentifier(m.name)) && m.name.text`
reads `m.name` three times, and the second and third reads are the first
one's slot, at the union of the two guards' arms where the condition holds.

A cell fact ($`x.f\mapsto R`$, read by `read-sliced`) states a predicate of a
location's current value, which survives a write a
[separation fact](PROGRAM-TYPING.md#separation-facts) separates from the
location; a read link states the value itself, whose every
refinement a linked read sees.

#### A guard on any argument

A listed guard's call of one argument evaluates the argument once, into a
slot $`s`$, and is the membership test of $`s`$, or of its tag field, after
the domain obligation on $`s`$:

```math
\frac{g\ \text{a node guard of}\ F,\quad K_g=\{t_1,\ldots,t_n\}}
     {g(e)\ \leadsto\ s\leftarrow e;\ \ s : P\ \text{checked};\ \ \mathsf{member}(K_g,\ s.\tau)}\ \textsf{host-guard-operand}
```

and a tag guard's call is $`\mathsf{member}(K_g, s)`$. A call on an
immutable name is the case where $`s`$ is the name's slot (`host-guard`). The
entry makes the call and the test agree: on its domain the guard returns
`true` exactly when the tag is in $`K_g`$, reads nothing but the tag and has
no other effect, so evaluating the argument and testing its tag is the call.
The argument's evaluation is the call's, its exceptions the call's. So
`ts.isIdentifier(m.name)` refines the slot of its read of `m.name`, which the
next read of `m.name` is by `read-linked`. The guard's signature
(`guard-value`) remains the reading of a guard used as a value. A
user-defined guard's call on a member path refines the slot of its read the
same way where the call keeps the heap
([a call that keeps the heap](PROGRAM-TYPING.md#a-call-that-keeps-the-heap)),
the path's witness holding the value the call was passed.

#### Entries

Branch scopes hold an administrative **witness** for each member path read
by their condition, and for each member path an expression statement's call
passes as an actual: an assertion function's call narrows that read, the
witness's newest, from its return on
([a call that keeps the heap](PROGRAM-TYPING.md#a-call-that-keeps-the-heap)).
A read maps its result into the witness slot; a branch
edge checks the refined type of that slot and projects its read links.
A path not read on an incoming short-circuit edge has the top type and no
read link on that edge. Witness names cannot occur in source identifiers.
The slots contain saved values; a later source member read is checked by
`read-linked`. Paths compose through the witnesses of their prefixes.

Every statement-entry witness link states the result of an ordinary property
read, including `undefined` where the key is absent. The slot's type is
checked separately on each incoming edge. Root annotations and explicit
presence predicates establish own-key requirements. A narrower saved-value
type uses the same ordinary-read relation at successive entries
(`blocker-round-conditional-path-reuse`, `blocker-round-receiver-path-reuse`).
A link through a present key establishes this relation
(`LinkClasses.holds_optional`); strengthening the relation to require a
present key requires independent evidence.

A statement entry states a path's refinement through the
[current-content assertion](SOURCE-CLAIMS.md#current-content-assertions) of
its root, a path of one member or more:
`{"name": "n", "type": […], "current": [[["expression"], [PropertyAccessExpression]], [["expression", "expression"], [Identifier]]]}`.
A refinement of a path $`p = x.f_1\cdots f_n`$ beyond the declared read
contract and the supported field predicates uses a witness slot $`w_p`$ at
the asserted type, with a checked read link $`r.f_n\mapsto w_p`$ whose
receiver $`r`$ is the root binding's slot for $`n = 1`$ and the witness slot
of the prefix $`p' = x.f_1\cdots f_{n-1}`$ otherwise. An entry holding a
witness of $`p`$ holds one of each of its prefixes, at the prefix's asserted
type or, where none is asserted, at its declared read from its own prefix's
type, so a path is a chain of links, one per segment. An asserted
refinement outside the primitive predicates that the declared read already
implies, where a tag refinement of the root leaves arms stating the member
required, also has its witness at the asserted type. The entry passes on the
ordinary-read relation of the test that read the path, which a later entry whose root claim no longer
implies the refinement needs (a loop's update after a guarded branch
rejoins, `blocker-compiler-api-parent-loop`; a write of the root in the
branch ends the link, `invalid-compiler-api-parent-loop-write`). The entry
keeps that witness only where an entry the flow reaches from it, by one or
more steps of the function's control-flow graph, has its own witness of
the path or of a longer path it begins, whose chain of links includes the
path's (`blocker-compiler-api-grandparent-loop`); elsewhere it asserts the field's contents, which the declared
read establishes, and an edge after a call that discards the link need not
carry it (`compiler-api-optional-field-join`). Every incoming edge,
including a loop backedge, checks each mapped witness's type and each link's
receiver and field, segment by segment. The rule is
[witness-edge](PROGRAM-TYPING.md#witness-edges), proved by
`ControlFlow.witness_edge_sound` for any receiver slot. Calls and writes
discard read links but those of [stable links](#stable-links), segment by
segment, so a path's chain survives a call where every segment is stable;
closure entries and exceptional transfers establish none. A catch therefore
cannot receive a witness link from the throwing computation. In a
condition, a path's read whose receiver was read just before, into its
prefix's witness as well, reads its field from that witness, which holds the
same value, so the link it records is the one the entry states. A strict
test of a path of two members or more against `null` or `undefined` re-reads
the path's last member into a saved slot and dispatches on it; that slot is
the path's witness on both edges, so the test's slice of it is the witness's
type (`field-write-refinement`; `invalid-path-null-test-alias`, a write through
an alias between the test and the read, run under Node). Controls:
`compiler-api-entry-path` (two and three members, a loop's backedge, past a
call), `invalid-compiler-api-entry-path-record` (a middle member a call
replaces, run under Node). An assertion of a path of two members or
more where the entry holds no witness of it is the premise of nothing.

#### Paths rooted at a slot

A `let` or an assigned parameter $`x`$ with $`\mathrm{slot}(x)`$
([slot or cell](SOURCE-ELABORATION.md#mutable-bindings-and-module-constants))
is a variable of its activation's environment, which a write rebinds and no
other step reaches. A path may start at it as at an immutable binding: its
reads record read links from the slot, its tests refine the reads' slots,
and statement entries hold its witnesses, each checked on every incoming
edge. A write $`x = e`$ rebinds the slot to the written value $`v`$; the
edge out of the write maps $`x`$ to $`v`$, so a link whose receiver is the
slot's previous value names no slot of the target frame:

```math
\frac{\mathrm{slot}(x)\quad \Gamma;\Pi;\Sigma\vdash_G v\leftarrow e : V\dashv\Pi';\Sigma'}
     {\Gamma;\Pi;\Sigma\vdash_G x = e\ \dashv\ \Gamma[x\mapsto V];\Pi';\ \Sigma'\setminus\{x.f\mapsto y\}}\ \textsf{slot-path-write}
```

So a path's refinement holds from its test until the root's next write on
every path into the read: a write between them, one on a loop's back edge
into a loop head that states the refinement, and one in a `try` block whose
`finally` reads the path each leave an incoming edge without the link, which
[witness-edge](PROGRAM-TYPING.md#witness-edges) refuses. A write of $`x`$
is its statement's own (a write nested in an expression makes $`x`$ a
cell): the assignment or update an expression statement is, or a target of
a destructuring assignment, whose later targets and defaults run after the
write and read $`x`$ from the rebound slot. A slot is environment, so a call keeps the root, and a link
through it survives the call where it is a [stable link](#stable-links); a
`let` written by a closure is a cell, whose read is a plain read link that a
call ends. The rule adds no trust: the links are the checker's, and the slot
lowering is the one the slot's own tests rely on.

Controls: `slot-path` and `compiler-api-slot-path` (within one condition
after a loop's writes, across statements, a retest after a write, past a
call through stable members); the negatives `invalid-slot-path-write`,
`-loop`, `-finally`, `-pattern` (a destructuring's default after its write
of the root), `-closure`, `-alias` (a member an alias replaces) and
`-call` (a call through a program record's member), each run under Node.

#### Stable keys

A record clause states a set $`\sigma`$ of **stable keys**, each one of its
readonly members, a view or an optional readonly field. The notion belongs
to no family: an object meets them when it reads each $`f\in\sigma`$ one
way for its life, owning $`f`$ at a location whose contract $`c`$ is
**stable**, or lacking both $`f`$ and a prototype:

```math
\mathit{flds}(f)=l\ \Rightarrow\ \exists v_0.\ \forall j, U, u.\ c_j(U,u)\Rightarrow u=v_0
\qquad
\mathit{flds}(f)=\varnothing\ \Rightarrow\ \mathit{flds}(\mathsf{proto})=\varnothing
```

the same $`v_0`$ at every level and world, $`c=W(l)`$. An object's map of
locations is part of its value, which no step changes, so whether it owns
$`f`$ never changes; an absent $`f`$ of an object without a prototype reads
`undefined` (`Step.readMissing`) in every heap. A stable key at a view is
owned, since the view requires the location; one at an optional field is
owned or absent, and stays so. Extension keeps every contract of a world
and truncation restricts it, so both keep a stable key. Subtyping
may forget a source's stable keys and proves every key the target states
stable; an ordinary record states none, so a node remains below
`{ readonly flags: number }`. A meet states the keys either operand states;
a join, such as a [residual](#residuals), the keys every operand states.

The semantic predicate `stableKeysT` in
[Types.lean](../lean/Verification/Types/Types.lean) states the requirement,
each key's reading by `StableAt`. `stableKeysT_at` supplies the object and
its reading, `StableAt.present` a present key's stable contract;
`stableKeysT_adm`, `stableKeysT_weaken` and `stableKeysT_append` prove
admissibility, forgetting keys and conjunction.
`ReadGave.stable_frame` in
[HeapFacts.lean](../lean/Verification/Semantics/HeapFacts.lean) frames what a
read of a stated key gives on normal return. A record or
dictionary clause states its stable keys (`Clause.refs`'s last part), whose
meaning is `stableKeysT` (`semWithArgs_stable`). In the declaration document
an object term states them as `"stable": [key, …]`, nonempty, which
`objectClause` decodes: a marked term's keys are its readonly members,
required or optional, and an unmarked term's, a program record's
[`@stable` fields](POSITIVE-TYPES.md#records), are its required readonly
fields.

The program never introduces a stable key: an allocation's locations have
the contracts of their types, which state no single value. A family's
reading is the one authorized introduction, at host values, by F1′. The
checks split by who can make them:

- **The trusted front end** writes a stable key only for a member the
  active family's reading authorizes: a property member, required or
  optional, of the shape the description's table selects, not among the
  description's exclusions. The interpreter refuses a description whose
  stable-member rule names an excluded member or one the shape lacks.
  The overlay of library types states one more, a typed array's
  `[[viewLength]]`, by the host assumption on views
  ([trust surface](DESIGN.md#trust-surface)).
- **Lean** accepts stable keys only on an object term carrying a family's
  marker, and only each a readonly member of that term, a view or an
  optional readonly field; a stable key at a writable member or at a key
  the term does not state is refused by the decoder. The claims
  structures (`Source/Claims/Wire.lean`) have no form for them, so a type
  the front states at a point carries them only by naming a declaration.

No program allocation owns `[[host]]`, so no program object meets a type
stating a stable key, whatever claim names one.

The stable members of a shape are those the description names: property
members of the shape, required or optional, the tag and a correction's
optional members among them. A method is none, nor a member the
description omits, nor a member of a program record, of a look-alike
declaration, of a host view (`Type`, `Symbol`, `Checker`, `API`) or of a node
list. Spelling (`readonly`, a member name) makes nothing stable.

#### Stable links

A read link $`x.f\mapsto y`$ through a member $`f`$ every arm of its
cell's claim states stable holds through every step, an optional link (a read of a member the object
may lack) among them, and so does a cell fact of such a read
([linked reads](#linked-reads)): the rule
[stable-link](PROGRAM-TYPING.md#checked-expression-postconditions), for
every term $`t`$, a call, a write or a closure's run, on the term's normal
return. A claim with an arm that does not state $`f`$ stable keeps no link
through $`f`$.

It is sound by a frame property of stable keys. An absent stable key of an
object without a prototype reads `undefined` from the object's value
alone, so its read gives `undefined` in every heap. A present one is a
location whose contract is stable: let $`c`$ be stable at
$`v_0`$ in $`W`$ at level $`n+1`$. A heap meeting $`W`$ holds $`v_0`$ at
$`c`$'s location; every state an execution reaches at a positive remaining
level $`m`$ meets a world extending $`W`$ truncated to $`m`$, whose
contract at that location is $`c`$ restricted to the levels below $`m`$, so
its heap holds $`v_0`$ there too:

```math
\frac{\mathrm{lookup}(W,\ell)=c\quad c\ \text{stable at}\ v_0\quad \mathrm{HeapOk}(n{+}1,W,h)\quad \mathrm{SafePost}(T,Q,n{+}1,W,h,t)}
     {\mathrm{SafePost}(T,\ \lambda h'\,v.\ Q(h',v)\land h'(\ell)=v_0,\ n{+}1,W,h,t)}\ \textsf{stable-frame}
```

The semantic lemmas are
`HeapObservations.stable_frame` in
[HeapObservations.lean](../lean/Verification/Semantics/HeapObservations.lean)
and `ReadGave.stable_frame` in
[HeapFacts.lean](../lean/Verification/Semantics/HeapFacts.lean), which
frames a read's result, present or absent. The checker applies the rule to
every step: each step's output keeps the input's read links and cell facts
through a member every clause of the receiver's type states stable
(`HeapExpressionRules.withStable`, `stableLinks` and `stableCells`, proved
by `withStable_sound` from `ReadGave.stable_frame`), the one place every
expression checker passes through (`Checker.keepingStable`).

So $`v_0=\rho(y)`$, the value the link observed, and the location holds it
in every later heap; for an absent key, $`\rho(y)`$ is `undefined`, which
every later read gives. The root $`x`$ is a slot, which no step but a write of
$`x`$ rebinds ([paths rooted at a slot](#paths-rooted-at-a-slot)); a `let`
root held in a cell is read into a slot by a plain read link, which a call
or a write of the cell ends.

What the frame property covers is the model's execution. A call into
external code that receives the node, a callback of `forEachChild` or a
separately verified function, keeps the link in the model; that the runtime
external code leaves the member as the model does rests on F1′ (T1′) and the
external execution correspondence (T8), which the lemma does not prove.

The exceptional edge keeps no stable link: a handler's entry states the
facts its own claim states, and the ordinary postcondition gives an
exceptional continuation none, so a refinement read in a `try` block is not
a fact of its `catch`.

A footprint that preserves a location's contents is another sufficient
condition for keeping a link through a call
([exceptional footprints](SOURCE-ELABORATION.md#exceptional-footprints)); it holds
of the calls whose footprint is checked, where stability holds of every
admitted call.

A stable member is the [effects vision](#guard-recognition) at its
strongest: an operation whose result no step changes. A refinement of a
stable path survives every call, as a fact of an immutable value does, so
no call's footprint has to keep it.

#### What a family supplies, what it gets

Stable members are one mechanism, in which no family is named: the
stable-contract notion, the clause's stable keys and their subtyping, the
decoder's checks and the stable-link rule read no package, member or tag
name. A family supplies, in its description, data alone:

- the marker, which the decoder requires of a shape stating stable keys;
- the stable-member rule's exclusions, each a property member its owner
  declares, checked against the declaration as reviewed;
- its omitted members, whose reads give no one value for a node's life,
  omitted from every shape and checked likewise.

It gets, for every property member of its shapes, required or optional,
corrected ones included, that the rule does not exclude, a stable key in
the declaration document; the tag of a residual is stable where the tag
member of every shape it stands for is, and a residual's member where
every source member is, and with them the stable-link rule: a test of a
path through such members, the member present or absent, holds past every
call and write. A host view of the package, a node list and a member of a
program record state none, by the same rule. The compiler API's
description excludes no member (its omitted `jsDoc` and
`SourceFile.tokenCache` are no members of any shape,
[reading rule 1](COMPILER-API.md#reading-rules)); the
[string-tagged stand-in](#a-string-tagged-stand-in) excludes none, and a
run under a description excluding `Call.callee` refuses the read its run
without the exclusion verifies (the string-tagged family's control in
`tests/single-pass-controls.mts`).

#### Stable members: limits

A closure's entry states no read link and no witness, so a callback reading
`m.name.text` after a test of `m.name` outside the callback reads the
member's declared type. A node list's
element is no path segment.

#### Stable members: trust

Linked reads and guards on any argument add none: a read of a structural
input's member is a data property's by the caller contract, a read of a host
value's member is a read of its model (T4), and a guard's test is its
entry's (F3).
Stable keys add none beyond F1′: the stable readings of a host value's
stable members, required and optional, are F1′'s modeled realization of F2,
the introduction obligation of a stable key at a host value. F2 and F1′
cover optional members: the audit of the compiler API's implementation is
[stable members as readonly views](COMPILER-API.md#stable-members-as-readonly-views).
C4 reads every property member of every node of the corpus twice and again
after the entry point's token functions have run over its file, regression
evidence for F2.

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
  ([operations](#operations-and-their-obligations)), which
  admits no copy of a host object's own keys.
- **Callbacks:** a callback's argument has a marker only where the audited
  contract of the function passing it states a family type; a callback's
  result at a family type must be derived, as any result.
- **Guards:** a re-export of a guard resolves to the checked binding; a
  program function calling a guard is an ordinary verified function, whose
  own promise, if it states one, is proved at its body.

Controls, the refused ones with their counterexample under Node where one
exists (`tests/compiler-api.mts`):

- verified: a program alias and a re-export of `Node` read as the family
  type; a generic identity function returning a node at `T`; a verified
  wrapper returning its node argument; a record's field holding a node read
  as the node (`compiler-api-family-identity`); a callback of `forEachChild`
  reading its node argument's members, and one returning the node it
  received (`compiler-api-node-callback`); a re-exported guard narrowing on
  both edges, a local function of a guard's name and a wrapper of a guard,
  each read at its own signature (`compiler-api-guard-calls`);
- refused: `{ node }` passed where a node is expected
  (`invalid-compiler-api-boxed-node`); `{ ...node }`, at the spread
  (`invalid-compiler-api-node-spread`); a program literal annotated as a node
  (`invalid-compiler-api-forged-node`); a callback of `forEachChild` whose
  result is asserted a node type it did not receive
  (`invalid-compiler-api-node-callback-result`); a read narrowed only by a
  guard's wrapper (`invalid-compiler-api-guard-wrapper`).

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
  every later step, and each of its stable members, required or optional,
  is owned at a location with a stable contract or, absent, absent from an
  object without a prototype. This is the model's side: what F2 says of the
  runtime, F1′ says of the world the run is checked in, and with F1 it makes
  the marker and the shape table correspond in both directions, which the
  agreement of two units' residuals needs. It is an external-model
  obligation, not a conjunct of `WorldAdm`.
- **F2 (runtime stability).** Each stable member, the tag among them,
  returns the same value on every read, and nothing the package or its
  clients do after creation changes it; an optional one is present with one
  value or absent, reading `undefined`, for the object's life.
- **F3 (guard identity).** Each guard table entry's statement (the exact tag
  set $`K_g`$, the tag the only member read, no other effect, an answer
  independent of further arguments and of the receiver, and the behaviour
  $`u_g`$ on `undefined` where the description admits its kind) holds of the
  function Node runs for its export identity, resolved as the entry records,
  under the audited digest. Activation reads that resolution from the
  verifying process's Node; F3 assumes the program runs under the same Node
  configuration (its conditions), through ES module resolution, over the
  unchanged installation, with no hook or loader altering resolution. The
  installation is trusted code: the front end executes it to parse the
  program before activation runs. Activation establishes that the reviewed
  table describes that installation as Node loads it, a consistency check
  under these assumptions; it is no defence against an installation
  modified before the front end starts, or a process whose loaded modules
  differ from their files. No guard's declared predicate is trusted: a
  listed guard narrows by its entry and every other narrows nothing. The
  generator and the front end's analysis are no part of the trusted base;
  the table and its review are.
- **F4 (transparent tag reads).** A read of the tag runs no code and throws
  nothing.
- **F5 (unwritten constants).** The enum objects and the module bindings in
  the guard table's recorded dependency closure are never written after the
  package loads, by the program or by external code (the package builds its
  enums as ordinary mutable objects and freezes nothing). A source write to
  them is refused by the existing rules: a write through a record or
  dictionary view of an enum object, `Object.assign` onto it, and a write of
  a namespace member or an import binding, each pinned by a control.

## Instances

### The compiler API

The description of `typescript` 7.0.2's syntax trees
([the node invariant](COMPILER-API.md#the-node-invariant)):

- package: `typescript` 7.0.2; entry point `typescript/unstable/ast`;
- installation: the package Node finds from `tools/`, and its declarations'
  digest (C0);
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
  `audited` for `JSTypeAliasDeclaration` and `JSImportDeclaration`
  ([audited shapes](COMPILER-API.md#audited-shapes));
  `base` `NodeBase` (`Count`);
- corrections: the [corrections](COMPILER-API.md#corrections) table;
- marker: `"RemoteNode"`;
- omitted members: `Node.jsDoc`, which builds a fresh array on each read,
  and `SourceFile.tokenCache`, which the entry point's token functions
  assign on the file they are given (reading rule 1);
- footprints: the callback-free node methods of
  [node methods and callbacks](COMPILER-API.md#node-methods-and-callbacks),
  `empty`, and `forEachChild`, `callbacks`, under T3;
- stable members: every property member of a shape, required or optional,
  no exclusion; checked by C4;
- guards: the table of the exports of `typescript/unstable/ast` whose
  functions, in `dist/ast/is.generated.js` and `dist/ast/is.js`, meet the
  recognition contract; `isLeftHandSideExpression` and `isUnaryExpression`,
  which read `expression`, get no entry.

Its rows are T1 (F1 and F2), T1′ (F1′), T2 (F3 and F5) and T4, which includes F4
([the compiler API's trust](COMPILER-API.md#trust)).

### A string-tagged stand-in

A stand-in package, `string-family-fixture` (`pipeline/string-family-fixture/`),
shows the mechanism general over the package and the tag's primitive:
`tests/single-pass-controls.mts` activates it beside the compiler API's description by a
description of its own (`pipeline/string-family.mts`, its guard table the
generator's output), which names its package, its installation (the
package Node finds from `pipeline/string-family-fixture-project/`, through
the fixture link `node_modules/string-family-fixture`) and its digest, and
states the fields of every family description: its marker, root, tag,
table, guard table and the rest; under a description of another digest, or of an installation
Node does not find, its programs are refused. Its units are tagged by
`type`, a string, whose constants are the string enum `UnitType`; its guard table
lists `isName`, an equality, and `isExpression`, through a helper of its
tag, which throw on `undefined`, and `isNameType`, a tag guard of the string
enum answering `false` there, each activated over the stand-in's own
modules, its undefined inputs both kinds; `isNameLoosely`, whose
answer depends on an option argument, takes two parameters and has no
entry, nor has `isNameOrAbsent`, which answers `true` on `undefined`, nor
have `isNameOptional`, `isSameType`, `isConstantType`, `isParenthesizedType`,
`isNameOfConstant` and `isCallAfterConstant`, outside the grammar
([undefined arguments](#undefined-arguments)). Each listed guard's call is the membership test of the family's
string constants and narrows both edges; the unlisted one narrows nothing.
Its description states no stable-member exclusion, so a callee tested and
read past a call verifies; under one excluding `Call.callee` the same read
is refused, under one excluding `Literal.type` no residual standing for
`Literal` states its tag stable, and under one listing `Unit.notes` as
omitted a read of it is refused (`pipeline/string-family-fixture-project/`,
where Node and TypeScript resolve the stand-in's specifier alike).

### A conjectured instance: a readonly Babel interface

A conjectured instance, which no description implements. Babel's nodes are plain objects that transforms
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
- stable members: every required property member. F2 then needs a lifetime shape
  preservation assumption the interface makes true: the client reaches nodes
  only through the parser's result and the readonly shapes, which grant no
  write, and the parser writes no node after it returns;
- guards: `lib/validators/generated/index.js`, whose bodies are
  `if (!node) return false; if (node.type !== "Identifier") return false;
  return opts == null || shallowEqual(node, opts);`. The guard syntax would
  gain the null test and the `opts` parameter, a call passing it refused: an
  extension of the one syntax, which every family then reads.
