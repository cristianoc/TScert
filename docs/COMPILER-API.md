# The compiler API as a host library

The front end's own functions (`tools/*.mts`) read TypeScript's syntax trees
through `typescript/unstable/ast` and its checker through
`typescript/unstable/sync`, from the package `typescript` 7.0.2 that
`tools/package-lock.json` pins. This document specifies the contract under
which such code is verified: how the package's declarations are read, the
audited corrections where a declaration cannot be its own contract, the
assumptions the result is relative to, and the restrictions it imposes. The
node invariant, the guards, host objects and stable members are the first
instance of the general mechanism of [host families](HOST-FAMILIES.md), which
owns their rules; this document gives the instance's data. The
prerequisites are the reading of declarations in
[Source contracts](SOURCE-CONTRACTS.md), the record clauses of
[Positive types](POSITIVE-TYPES.md#records), the array invariant of
[Semantics](SEMANTICS.md#the-array-invariant) and the source model's
[arrays](SOURCE-MODEL.md#arrays). The supported members follow the front
end's actual use, through the method of
[modeling a library](SOURCE-CONTRACTS.md#modeling-a-library). General compiler
construction, caller-selected backends and registration of retained callbacks
are outside this source interface; incoming instances satisfy the external
contract stated below.

## The contract in brief

The package's declarations are read **on use**, through the declaration
reader's existing collection: the names a unit imports are roots, followed
through the declarations they reach. A reviewed contract,
`tools/compiler-api.mts`, adds what a declaration cannot state. The contract
states one invariant for syntax trees and derives the guards from it.

- **The node invariant.** A node of kind $`k`$ has the shape $`S_k`$ that the
  declarations give kind $`k`$, and its fields never change. The type `Node`,
  and every node type whose `kind` is no set of literals (`Expression`,
  `Statement`, `TypeNode`, …), is the union of the shapes below it,
  discriminated by its readonly field `kind`.
- **Guards are kind tests.** `ts.isX(e)` is the test
  $`e.\mathtt{kind}\in K_X`$, with $`K_X`$ the kinds the guard's
  implementation accepts, read from its body by a check over a small syntax.
  A call is the membership test `tagMember` of the kind against $`K_X`$,
  which narrows both edges by the `member-yield` rule
  ([guard recognition](HOST-FAMILIES.md#guard-recognition)).
- **Everything else is the declaration**, read by five general rules for
  host declarations: stable members are readonly views and a member whose
  reads give no one value for a node's life is refused; an `any` member is an optional `unknown`; a
  numeric enum type at a package position is `number`; each host class is
  read through a named view; branded strings are opaque host-introduced
  types. Values of host types come from the package alone.
- **Corrections** state the ten fields the declarations call required and
  the runtime leaves absent.

## The package at run time

The runtime details concern the package's `dist/` files in `typescript`
7.0.2. The Node measurements are dated 2026-10-16.

- **Nodes** are instances of one class, `RemoteNode`, whose fields are
  getters decoding an immutable buffer the server sent (`get kind()` reads
  `view.getUint32`). Which named children a kind has is the generated table
  `childProperties[kind]`; a child whose presence bit is clear reads
  `undefined`. Children are created lazily and memoized per source file, so
  two reads of a child field give the same object. One getter allocates:
  `jsDoc` builds a fresh array on each read (`node.generated.js:221`); every
  other getter of `RemoteNode`, `RemoteSourceFile` and `RemoteNodeBase`
  returns a primitive or a memoized object. No getter backs
  `SourceFile.tokenCache`, which the entry point's token functions
  (`getTokenAtPosition`, `getTouchingToken`, `getTouchingPropertyName`,
  `findPrecedingToken`, `findNextToken`) assign on the file they are given
  (`astnav.js:510-513`): absent, then a `Map`. The class's data fields
  (`parent`, `view`, `index`, `_byteIndex`) are writable and written only by
  the constructor; `RemoteSourceFile` passes `undefined` as `parent`
  (`node.js:34`).
- **Node lists** are `RemoteNodeList`, a subclass of `Array` whose static
  `Symbol.species` returns `Array`, whose `length` is a writable own data
  property, and whose elements 0–15 are getters on its prototype and 16
  onward own getters, all returning `this.at(i)`. It overrides `at` (a
  non-integer index gives `undefined`) and `Symbol.iterator`. Its `pos` and
  `end` are getters of its prototype, without setters, reading its buffer;
  `transformFlags` and `hasTrailingComma` are own data fields the
  constructor leaves at 0 and `undefined`, a trailing comma's list
  included, and no other code of the package names them
  (`node.generated.js`). On a source
  file's `statements`: index 0 is no own key; `for…in`, `Object.keys`,
  `Object.entries` and an object spread enumerate the class's fields
  (`parent`, `view`, `sourceFile`, `_cursorIndex`, …) and no index; `5 in
list` is true for a three-element list (a prototype getter) while `list[5]`
  is `undefined`; writing an index or `push` throws (a getter without
  setter); `JSON.stringify` throws (a cycle through `parent`);
  `Array.isArray` is true; `map` returns a plain array; iteration, indexing
  and `Array.from` agree.
- **`forEachChild(visitNode, visitList)`** walks the buffer, calls the
  visitor on each child (JSDoc skipped), returns the first truthy result and
  otherwise `undefined`. It reads nothing a client can write.
- **Enums.** The package's `imports` map sends `#enums/*` to
  `dist/enums/*.enum.d.ts` under the `types` condition and to
  `dist/enums/*.js` under `default`, which Node loads. Against those runtime
  files, 996 of the 997 literal members of the 27 `.enum.d.ts` files match;
  `CharacterCodes.ogham` is 5760 in `characterCodes.enum.d.ts` and 5765 in
  `characterCodes.js`. `SyntaxKind` has 386 member names over 352 distinct
  values (the `First*`/`Last*` aliases). The flag enums (`NodeFlags`,
  `TypeFlags`, `SymbolFlags`) hold bitwise combinations at run time, which
  are no member's value.
- **Guards.** `ast` exports 352 functions named `is*`. Executed on every
  `SyntaxKind` value with a recording argument, 309 read only `kind`; of
  their accepted kind sets, 300 equal the kinds of their declared predicate
  type, 6 have a predicate whose `kind` is all of `SyntaxKind`
  (`isExpression`, `isStatement`, `isTypeNode`, `isBlockOrExpression`,
  `isConciseBody`, `isForInitializer`), and 3 accept kinds their predicate
  excludes: `isTypeAliasDeclaration` accepts `JSTypeAliasDeclaration` (345),
  `isImportDeclaration` and `isAnyImportSyntax` accept `JSImportDeclaration`
  (346). Two more read `expression` (`isLeftHandSideExpression`,
  `isUnaryExpression`); 34 take a kind number (29 with predicates such as
  `kind is AdditiveOperator`, 5 Boolean); 7 test scanner characters. On a
  JavaScript file with `/** @typedef {{ a: number }} Pair */`, a function
  typed `(node: Node): SyntaxKind.TypeAliasDeclaration | undefined`
  returning `isTypeAliasDeclaration(node) ? node.kind : undefined` returns
  345.
- **Declared shapes.** Over 182,305 nodes of 1,115 files (`tools/*.mts` and
  `pipeline/examples/*.ts`), every child's kind is within its declared field
  type, and eight declared-required fields are absent:
  `PropertySignatureDeclaration.initializer` (2,377 nodes),
  `PropertyAssignment.type` (3,819), `ShorthandPropertyAssignment.type`
  (454), `ExportAssignment.type` (1), `DefaultClause.expression` (24),
  `NoSubstitutionTemplateLiteral.rawText` and `.templateFlags` (2), and
  `SourceFile.parent` (every file; `Node.parent` is declared required).
- **Kinds and declarations.** Of 352 kinds, 193 are the `kind` of exactly
  one non-generic interface, `PropertyAccessExpression` of three (the
  interface and two refinements extending it), 153 token and keyword kinds
  only of the generic families `Token<K>`, `KeywordTypeNode<K>` and their
  kin, and 2 (`JSTypeAliasDeclaration`, `JSImportDeclaration`) of none.
  `Count` is a marker. 29 interfaces have `kind: SyntaxKind` (the abstract
  bases); 14 of them declare fields beyond their brand.
- **`any`** occurs as the 15 brand fields of the abstract bases
  (`_expressionBrand: any`, …), `Path`'s `__pathBrand`, and
  `SyntheticExpression.type`. No runtime node has a brand property.
- **Types and symbols** are instances of `TypeObject` and `Symbol`, with
  readonly data fields and methods that fetch from the server synchronously.
  `isUnionType()` is `(this.flags & TypeFlags.Union) !== 0`; `getTypes()`
  returns `undefined` unless the type is a union, an intersection or a
  template literal type. For those types, `ProjectObjectRegistry.fetchTypes`
  returns a fresh array, populated by index when handles are cached and by
  `map` over the server's type data otherwise (or `[]` for null data).
- **Node builders.** The factory (`./unstable/ast/factory`), the clones
  (`getSynthesizedDeepClone`, `getSynthesizedDeepClones`) and the visitors
  (`visitNode`, `visitNodes`, `visitEachChild`, and the handwritten
  `visitEachChildOfJSDocParameterTag` and `visitEachChildOfJSDocPropertyTag`
  in `dist/ast/visitor.d.ts`) return `NodeObject`s the
  package builds, whose root's `parent` is `undefined`
  (`factory.generated.js:13`, `clone.js:56-78`, `visitor.js`, whose JSDoc
  visitors call factory updates) where every shape but a
  source file's requires it; so does the root `decodeNode` builds for the
  sync API's `typeToTypeNode` and `signatureToSignatureDeclaration`
  (`node.js:284`), which no view lists.
- **Retained callbacks.** `new API({ fs })` registers the client's
  `readFile`, `fileExists` and other `fs` functions with the channel
  (`client.js:38`); the server calls them back synchronously during later
  requests. One `updateSnapshot` of a one-line file calls `readFile` 179–191
  times, a changed-file snapshot once more, checker queries none; the
  arguments are strings. A callback that throws, calls the API reentrantly,
  or returns a value outside its declared type makes that request throw
  (`Error calling callback`, `EPIPE`, `Unexpected EOF`) and every later
  request of the instance throw; nodes already obtained stay readable.
- **Snapshots and lifetimes.** Objects are memoized per snapshot: two
  `getSymbolAtLocation` calls give the same `Symbol`, two `resolve()` calls
  the same node, in another file too. On a file whose two declarations are
  swapped between snapshots, a node of the old snapshot asked of the new
  checker gives the type of the node at the same index in the new tree
  (`"x"` for `1`); `NodeHandle.resolve(project)` with the new project gives
  the new tree's node at the handle's index; an old `Symbol` asked of the
  new checker throws (`symbol handle 1 not found`); the old checker answers
  until its snapshot is disposed, and then throws (`snapshot 1 not found`);
  nodes of a disposed snapshot stay readable. A node of one `API` instance
  asked of another instance's checker gave the type of the declaration at
  the same path. Results are values of the declared types or throws, and
  need not describe the node passed.

## Host declarations

A **host package** is a package the contract names: `typescript`, with the
modules `unstable/ast` and `unstable/sync`. Its declarations are the files
of the audited installation, which the family description names
([activation](HOST-FAMILIES.md#activation)): the package `typescript` Node
resolves from `tools/` (`tools/package-lock.json` pins it), whose `.d.ts`
files have the description's digest (C0): a package elsewhere, whatever its
manifest names, gets no host reading, and a changed installation is refused
until reviewed again. A **host type** is a type the
contract lists as introduced by the package alone: every node shape,
`NodeArray`, `Type` and its sub-interfaces, `Symbol`, `Signature`,
`NodeHandle`, and every class the package declares (`API`, `Snapshot`,
`Project`, `Program`, `Checker`, `Emitter`). The option interfaces the
client fills (`APIOptions`, `UpdateSnapshotParams`, `DocumentIdentifier`)
are ordinary types.

### Reading rules

1. **Stable members.** A member of a host type whose read returns the same
   value every time (a data property the package writes only in its
   constructor, or a getter decoding the immutable buffer and returning a
   primitive or a memoized object) is a **readonly view**, whether or not
   its declaration is `readonly`, so a client write to it is refused, and
   an optional one is as stable as a required one
   ([below](#stable-members-as-readonly-views)). The contract lists the
   members whose reads give no one value for a node's life, `jsDoc`, whose
   read allocates, and `SourceFile.tokenCache`, which the package assigns on
   a file it built earlier, each omitted from its host type's shape. Every form that
   reads it is then a read of a member the type does not state, refused by
   ordinary typing whatever its key's spelling: `o.m`, `o?.m`, `o["m"]`, a
   key a constant holds or a template computes, a pattern's key. A
   structural type stating the member, `{ m?: T }` included, admits no value
   of the host type, since width subtyping into an optional field is
   refused. `"m" in o` reads no member's value and runs no getter.
2. **`any` states nothing.** A member declared `any` is an optional member
   of type `unknown`. A brand is such a member; reading one gives
   `undefined`.
3. **Enums.** A host enum $`E`$, a `declare enum` the package's modules
   export through the `#enums/*` imports and the contract lists, is read by
   the `emitted-enum` rule ([enums](SOURCE-CONTRACTS.md#enums)): the value
   `E` is $`\mathcal O^{\rho}(E)`$, whose runtime object C1 checks against
   the declaration, and `E.M` the literal type of `M`'s value. The
   type `E` of an enum with a numeric member at a position of a host
   declaration is `number`, since TypeScript admits any number at a numeric
   enum type and the flag enums hold combinations there; that of an enum of
   strings alone is the union of its members' literals, which are all
   TypeScript admits there. A literal member type `SyntaxKind.Identifier`
   is the literal. Reading an enum as a value requires the import, resolved
   by Node from each importing module through program re-exports, to bind
   the object C1 checks ([activation](HOST-FAMILIES.md#activation)).
4. **Named views.** A host class (`Checker`, `Program`, `Snapshot`,
   `Project`, `API`, `Symbol`, `NodeHandle`, `Signature`) and a host
   interface the contract names (`Type`, `ThisTypePredicate`,
   `AssertsThisTypePredicate`) are read through a view
   that `compiler-api.mts` names and lists: the members the front end uses,
   each with its reviewed declaration text. A view is a contract of its own,
   with the introduction obligation $`⟦H⟧\subseteq⟦\mathsf{view}(H)⟧`$,
   which holds because each listed member is read exactly as declared and a
   record states nothing of the keys it does not name. Host values reach
   the client only from the package, so the client never produces a view.
   A read of a member outside the view is a located refusal naming the
   view, the member being no member of the type its view reads, and adding
   it is a reviewed edit. The view is the type's whole shape: it inherits
   nothing, and a declaration merged into a host type from outside the
   audited installation (a project's module augmentation) is refused where
   the type is reached. An overloaded member is the overloads its view lists; a
   host class without a view has no member. A view lists no constructor or
   static member: a host class's value is read as a record of no member,
   whose type parameters it does not name, and `new` of it is a located
   refusal naming the view. Node shapes are read member-complete. Read
   member-complete, `Checker` alone brings 50 methods whose types reach
   `CompletionInfo`, `Uint8Array` and `ReadonlyMap<__String, …>`, and 38
   `this is X` methods (counted on 2026-10-16). `Type`'s view lists none of its `this is X`
   methods, whose predicates the [stated type guards](#stated-type-guards)
   state as functions.
5. **Branded strings.** `Path` (`string & { __pathBrand: any }`) and
   `__String` are opaque host-introduced types whose values are strings:
   reading one gives a string, and a host parameter of such a type admits a
   value the package produced at that type, so a round trip is admitted and
   an arbitrary string is not. The calculus has no opaque primitive type, so
   every position where the client would produce a branded value is
   refused, a host parameter among them, and a host-produced one is read as
   a string. The reader keeps a branded string's identity until the
   direction of its use is known (`hostBrands`): in a value or a member of a
   host type, an occurrence where the host produces the string (a result, a
   readonly member, a callback's parameter) is `string`, and one where the
   client would produce it (a host function's parameter, a callback's
   result) or where the direction is unknown (a writable member, a type
   argument, a binder's bound) is refused. A client annotation or an alias
   naming the brand keeps its declared definition, which no value meets, and
   is refused where it is used. The branded aliases are `Path` and
   `__String` of the audited host files, each checked against its reviewed
   text; the branded parameters are those of `getSourceFileMetadataByPath`,
   the internal registry's `getProject` and `unescapeLeadingUnderscores`.
   A symbol table, the result of `Symbol.getMembers` and `getExports`
   (`ReadonlyMap<__String, Symbol>`), is read as
   `ReadonlyMap<string, Symbol>` (`tableReading`): it is a native `Map`
   whose keys the package produced, and the standard `get` and `has` take
   any key, so a string the client produces reads the entry the map stores
   or nothing ([audits](#audits-of-sync-members)).

Overloaded methods of a declared class, several declarations of one name
without a body, are one member: the conjunction of their signatures, by the
`overloads` rule
([imported values](SOURCE-CONTRACTS.md#imported-ambient-and-global-values))
read per member (`classInstance`); a named view lists each overload it
admits, as `Checker`'s lists both forms of `getSymbolAtLocation` and
`getTypeAtLocation`. Private members are no members.

### Host provenance

Each host class $`H`$ of the runtime (`RemoteNode`, `RemoteSourceFile`,
`RemoteNodeList`, `TypeObject`, `Symbol`, `Signature`, `NodeHandle`,
`Checker`, `Program`, `Project`, `Snapshot`, `API`) has a key $`\kappa_H`$
that its prototype owns, as a class's $`\kappa_C`$
([derived source forms](SOURCE-ELABORATION.md#derived-source-forms)). Every
host type requires the key of its values through the prototype chain, which
$`\mathsf{hasKey}`$ walks. The key states a fact of the runtime, that these
objects have those prototypes, and it is preserved:

- an alias is the same object;
- an object literal, a spread, `Object.assign` onto a fresh target and
  every allocation from parts copy own enumerable data properties and give
  the result `Object.prototype` or no prototype; a class the client declares
  has its own prototype; the host prototypes are absent from the package's
  `exports` map, and the reflective operations that reach or set a
  prototype (`Object.getPrototypeOf`, `Object.create`,
  `Object.setPrototypeOf`, `__proto__` writes) are outside the admitted
  language or refused on a host value;
- by the reading of stable members below, every type a host value can be
  given keeps its stable members unwritable.

### Restricted values

The package's objects, its nodes, types, symbols, checker and `API`
instances, and its node lists, are the
[restricted values](HOST-FAMILIES.md#restricted-values) of host objects:
that section states their classification, their exclusion and the runtime
objects' difference from the model's reading, with this package's objects as
its examples.

### Stable members as readonly views

A record clause $`\mathsf{Ref}(\varphi;\psi;\omega;\mu;\beta)`$
([records](POSITIVE-TYPES.md#records)) has invariant fields $`\varphi`$,
which the write rule consumes ($`a.f\leftarrow a'`$ needs
$`(f{:}A)\in\varphi`$,
[judgments](PROGRAM-TYPING.md#judgments-and-constructor-views)), and
readonly views $`\psi`$. A view $`(f{:}A)\in\psi`$ holds of an object whose
field $`f`$ is a location whose stored contract implies $`⟦A⟧`$ at every
smaller index and world (`viewT`), and world extension preserves it
(`viewT_adm`): no alias writes a value outside the view. A stable member of
a host type is read as a readonly view:

- *Write.* The write rule consumes $`\varphi`$ alone; a view grants none.
- *Subtyping.* A view is below a wider view and is no invariant field, which
  states the stored contract exactly. So a node is below
  `{ readonly flags: number }` and outside `{ flags: number }`; a generic call
  instantiating a parameter bounded by `{ parent: Node }` at a node type
  fails its bound; a separately verified function taking `{ flags: number }`
  rejects a node, because the importer checks the argument against the
  declared parameter.
- *Narrowing.* A field test on a view drops the arms whose view answers the
  other way (`if-field`, [guards](SOURCE-ELABORATION.md#guards); Lean's
  `fieldSlice` and `fieldSlice_sound`, which take a view's location from
  `viewsT_at`). The exclusion concerns the object's label, which the stored
  contract fixes for the object's lifetime. A view of `length`, which an
  array's length meets too and which is no field location, narrows nothing.
- *Introduction.* A host value meets the view by T1.

A view states no equality between two reads: a readonly `parent` may give
different values. That stable members return the same value on every read,
an optional one present with one value or absent, is the host assumption
T1; no rule of the node shapes or the guards reads it, since a guard's
membership test reads `kind` once and the field slice's exclusion is
timeless.

**Optional members.** The audit of `typescript` 7.0.2's implementation, on
2026-10-22, of every property member a node shape states optional,
corrections included:

- a node's data is a `DataView` over a response payload, a fresh
  `Buffer.allocUnsafeSlow` with its own `ArrayBuffer`, filled once before
  the request returns (`syncChannel.js:404-417`, `readBin`) and written by
  no code afterwards; the fields holding it (`view`, `_byteIndex`,
  `_sourceFile`) are no shape's members;
- 47 child members (`initializer`, `type`, `name`, `body`, `modifiers`, …)
  are prototype getters of `getNamedChild` (`node.generated.js:293-303`),
  `undefined` where the kind's `childProperties` row lacks the name or the
  buffer's presence bit is clear, and otherwise the child memoized in
  `sourceFile.nodes`, which is written only at an empty index and never
  cleared (`node.generated.js:165, 281`; `node.js:43, 112`);
- `phaseModifier`, `rawText` and `templateFlags` are switches on `kind` over
  the buffer's bits, `undefined` at the kinds they lack;
- `fullSignature` and the brands have no getter and no own key, and nothing
  in the package assigns them: `undefined` on every read; `parent`, optional
  on `SourceFile` by correction, is an own data field the constructors
  alone assign (`node.infrastructure.js:84`), the package's other writes of
  `parent` (`clone.js`, `astnav.js`) being to objects it builds before
  returning them;
- `SourceFile.tokenCache`, which `astnav.js:510-513` assigns, is omitted
  (reading rule 1);
- source files are shared across snapshots only where content and parse
  options agree, and the cache that holds them never writes one
  (`sourceFileCache.js`).

C4 reads every such member twice on the corpus and again after the token
functions have run over each file.
[Stable members](HOST-FAMILIES.md#stable-members) are the one rule that
reads it.

A test of a member path refines the slot of its read, which a later read of
the same path is while its read link holds
([linked reads](HOST-FAMILIES.md#linked-reads)); a call or a write ends the
link. A link through stable members of node shapes holds through every step
([stable links](HOST-FAMILIES.md#stable-links)): their locations have
stable contracts by T1′, and the other host classes (`Type`, `Symbol`,
`Checker`, `API`) and node lists have no such assumption. The steps of a
`for...of` loop are among them: a node's field tested before the loop is
reread at the narrowed type after it (`blocker-compiler-api-field-guard`).

The refinements of `unknown` (`typeof`, `in`, `Array.isArray`) must give
readonly views or optional fields, so that no writable view of a host object
arises from `unknown` either. This is an obligation on the existing
refinement rules, which the provenance controls of the compiler-API cases
check. A
test finding a writable optional key present reads it as an invariant field
only on a record excluding host values, and as a readonly view otherwise
(`BranchRefinement.promote`).

## The node invariant

The node invariant is the [family contract](HOST-FAMILIES.md#the-family-contract)
of the compiler API's [description](HOST-FAMILIES.md#the-compiler-api). Let
$`\mathcal K`$ be the 352 values of `SyntaxKind`. For $`k\in\mathcal K`$
the **shape** $`S_k`$ is the record type with the marker `"RemoteNode"`,
`kind` at the literal $`k`$, and the members of the declaration the
description's table selects for $`k`$, with the
[corrections](#corrections) applied and reading rules 1–3. A node
type whose `kind` is no set of literals is the union of the shapes of its
members (`family-union`). `SourceFile` is a member of `Node`, although its
corrected shape is outside `Node`'s declared record. Every interface extends
`Node`, so $`\mathrm{members}(\mathtt{Node})=\mathcal K`$; `Expression` is
the kinds whose interfaces extend `ExpressionBase`, and `FunctionLikeBase`
the kinds whose interfaces extend it. The guard `isExpression` accepts a
different set (it excludes `JsxText`, which the declarations make an
expression), and `isTypeNode` accepts `ExpressionWithTypeArguments`, whose
interface extends `MemberExpressionBase` and no `TypeNodeBase`; the guard's
kind set serves the guard and the hierarchy the type, so a node `isTypeNode`
accepts is no `TypeNode` until its kind excludes 234
(`blocker-compiler-api-type-node`). A concrete union (`MemberName = Identifier | PrivateIdentifier`) is
read as declared.

### Arms per run

A run keeps the arms of the kinds its candidate modules' tests and types
name and one [residual](HOST-FAMILIES.md#residuals)
([the run's selection](HOST-FAMILIES.md#the-runs-selection)). A run naming
`Identifier` and leaving `SourceFile` to the residual gets `parent` optional
in its residual, since a source file's `parent` is absent. The shapes with
the same members and different kinds are the 15 modifier keywords and the
token families. Per top-level unit the kinds named are median 4, at most 57;
a run of a slice of `fragment-statements.mts`, which imports functions from
`fragment-support.mts`, reads `Node` with 47 arms (`abrupt`, 2026-10-19).
Through `verify-source.mts` at commit cbe2893 on 2026-10-16, a union of
$`n`$ record arms narrowed by `kind` took 1.2 s for $`n=20`$ and 9.4 s for
$`n=50`$, and exceeded the 30 s search limit for $`n=100`$; the cost of a
residual's `kind` is measured under [tag sets](HOST-FAMILIES.md#tag-sets).
Two units' readings agree for the values T1 and T1′ describe
([agreement across runs](HOST-FAMILIES.md#agreement-across-runs)).

## Guards

[Guard recognition](HOST-FAMILIES.md#guard-recognition) reads the guard
table, which its generator derives from the bodies in
`dist/ast/is.generated.js` and `dist/ast/is.js` as the package's `exports`
map resolves them. The tag field is `kind`, and a constant is a member of
`SyntaxKind` read through the module's import binding of `#enums/syntaxKind`,
which resolves under the `default` condition to the file whose values the
enum check compares with the declaration. The helper graph has depth 9 (the
`OrHigher` chain). A node's kind is in $`\mathcal K`$ by T1, so ranges
(`isTokenKind`'s `kind >= SyntaxKind.FirstToken && kind <= SyntaxKind.LastToken`)
are exact there. A guard taking a kind has a parameter of type `number`
(rule 3); the 29 such guards with a predicate use equalities and helpers,
and the 5 range helpers are Boolean functions without a predicate, read as
declared. The 326 guards of `is.generated.js`, read on 2026-10-16: 232 a
single equality, 35 a disjunction of equalities, 15 a `kind` constant and
equalities, 2 a `switch`, 8 a helper on the kind, 34 taking a kind; all are
in the syntax. `isLeftHandSideExpression` and `isUnaryExpression`
(`is.js`) read `expression` and are outside it.

A node guard's call refines its argument by the guard's kind set
([calls](HOST-FAMILIES.md#calls)): `isTypeAliasDeclaration(n)` refines `n`
to `TypeAliasDeclaration`'s shape or `JSTypeAliasDeclaration`'s
[audited shape](#audited-shapes), so `n.typeParameters` after it is read on
both arms and `n.kind` is either kind, and `isExpression(n)` to the 46
kinds the implementation accepts. A tag guard's call on a binding of a
`SyntaxKind` (`isAdditiveOperator(op)`) is the membership test of the binding
itself, which refines it on both edges.

Every node guard of the table reads `kind` first, so it throws a
`TypeError` on `undefined`; the description admits node guards'
behaviour on `undefined` ([undefined arguments](HOST-FAMILIES.md#undefined-arguments)),
so `isCallExpression(n.parent)` throws where `parent` is absent and holds of
a present `parent` on both edges. The tag guards answer `false` on
`undefined`; the description does not admit their behaviour there, so a
tag guard's argument stays within `number`.

## Corrections

`tools/compiler-api.mts` holds, for each field the declarations state
required and the runtime leaves absent, the interface, the field, the
declaration text it was reviewed against, and its reading as optional:
`PropertySignatureDeclaration.initializer`, `PropertyAssignment.type`,
`ShorthandPropertyAssignment.type`, `ExportAssignment.type`,
`DefaultClause.expression`, `NoSubstitutionTemplateLiteral.rawText`,
`NoSubstitutionTemplateLiteral.templateFlags`, `parent` on kind
`SourceFile`, `TaggedTemplateExpression.questionDotToken` (absent on an
ordinary tag`a`) and `JSDocTemplateTag.constraint` (absent on
`/** @template T */`). A correction makes a field optional; it adds no
field and narrows no type. Three are members a kind inherits
(`NoSubstitutionTemplateLiteral.rawText` and `.templateFlags` from
`TemplateLiteralLikeNodeBase`, `parent` of `SourceFile` from `Node`), which
only a member-complete shape states per kind.

## Audited shapes

A kind no declaration states as its literal gets an audited shape where the
review states one ([the family description](HOST-FAMILIES.md#the-family-description)),
and `NodeBase`'s otherwise (`Count`, the one such kind no node has).
`JSTypeAliasDeclaration` (345) has one: in a
JavaScript file the parser reparses each JSDoc `@typedef` and `@callback`
into a node of that kind, a statement of its file's or its block's
`statements`. Its shape extends `DeclarationBase`, `StatementBase` and
`ModifiersBase` and states `TypeAliasDeclaration`'s `name: Identifier`,
`typeParameters?: NodeArray<TypeParameterDeclaration>` and `type: TypeNode`,
each read at that declaration; its `kind` is 345. So it is a member of
`Node`, `Statement` and `Declaration`, and no value of type
`TypeAliasDeclaration` has it.

The audit of the runtime getters: a node of every kind is a `RemoteNode`,
whose child getters (`name`, `typeParameters`, `type`, `modifiers`) each
read through the kind's child list (`getNamedChild`,
`dist/api/node/node.generated.js:293-304`), absent where the node's child
mask lacks the child; the list of 345 is `TypeAliasDeclaration`'s,
`modifiers`, `name`, `typeParameters`, `type`
(`dist/api/node/protocol.generated.js:40-41`); `flags` reads the node's
record and `modifierFlags` folds `modifiers`
(`node.generated.js:821-833`), as for every kind. A present
`typeParameters` is a node list, of the [node lists'](#node-lists)
contract, whose elements are `TypeParameter` nodes. C3 checks the shape's members on every node of kind 345
of its corpus, `tests/node-shapes-corpus/script.js` holding `@typedef` and
`@callback` tags with and without `@template`, at the top level and in a
function's block: each required member present, each member within its
declared type, `typeParameters` a dense list of `TypeParameter` nodes where
present, and each member held by some node.

`JSImportDeclaration` (346) has one too: in a JavaScript file the parser
reparses each JSDoc `@import` into a node of that kind, a statement of its
file's `statements`. Its shape extends `DeclarationBase`, `StatementBase`
and `ModifiersBase` and states `ImportDeclaration`'s
`importClause?: ImportClause`, `moduleSpecifier: Expression` and
`attributes?: ImportAttributes`, each read at that declaration; its `kind`
is 346. So it is a member of `Node`, `Statement` and `Declaration`, and no
value of type `ImportDeclaration` has it.

The client's getters give a child exactly where the server encoded it: a
child getter reads through the kind's child list (`getNamedChild`,
`dist/api/node/node.generated.js:293-304`), absent where the node's child
mask lacks the child's bit, and otherwise the encoded node, whatever its
kind. The list of 346 is `ImportDeclaration`'s, `modifiers`,
`importClause`, `moduleSpecifier`, `attributes`
(`dist/api/node/protocol.generated.js:45-46`). So presence and kinds are
the server's. The package's `gitHead` is
`2bd066d87f5bafd315be9f40889d0a60b9e58e0b` of
[typescript-go](REFERENCES.md#typescript-go), version 7.0.2; at that
revision:

- **The nodes the client reads.** The server encodes three things: a
  program's source file (`handleGetSourceFile`, `internal/api/session.go:1045-1065`,
  `sourceFile := program.GetSourceFile(...)` then
  `encoder.EncodeSourceFile(sourceFile)`), and the results of
  `typeToTypeNode` and `signatureToSignatureDeclaration`
  (`session.go:2035-2105`), which no view lists. A program's file is the
  parser's result: `GetSourceFileByPath` returns `p.filesByPath[path]`
  (`internal/compiler/program.go:1817-1819`), filled from the host's
  `GetSourceFile` (`internal/compiler/fileloader.go:370`), which is
  `parser.ParseSourceFile(opts, text, …)` (`internal/compiler/host.go:83`)
  or, in a project, the parse cache's
  `parser.ParseSourceFile(key.SourceFileParseOptions, fh.Content(), key.ScriptKind)`
  (`internal/project/parsecache.go:34`, `compilerhost.go:96-100`). A
  program update replaces a changed file by a new parse,
  `newFile := newHost.GetSourceFile(oldFile.ParseOptions())`
  (`program.go:300-301`, `334-335`); the parser has no incremental
  reparse (`internal/parser/parser.go:1134`, `// !!! incremental parsing`,
  the reuse commented out). No code of the server assigns a parsed import
  declaration's `ModuleSpecifier`, `ImportClause` or `Attributes` outside
  its constructors (`data.ModuleSpecifier = moduleSpecifier`,
  `internal/ast/ast_generated.go:2530-2537`), and no code calls
  `setModifiers` (`internal/ast/ast.go:1523`). The transformers' and the
  language service's `UpdateImportDeclaration` calls
  (`internal/transformers/…`, `internal/ls/organizeimports.go`) build new
  nodes for emit and edits, which no program file holds.
- **Construction.** In a parse, a node of kind 346 is made at one site, the
  reparse of a JSDoc `@import` tag (`internal/parser/reparser.go:119-133`):

  ```go
  case ast.KindJSDocImportTag:
      importTag := tag.AsJSDocImportTag()
      if importTag.ImportClause == nil {
          break
      }
      importClause := p.addDeepCloneReparse(importTag.ImportClause)
      …
      importDeclaration := p.factory.NewJSImportDeclaration(
          p.factory.DeepCloneReparseModifiers(importTag.Modifiers()),
          importClause,
          p.addDeepCloneReparse(importTag.ModuleSpecifier),
          p.addDeepCloneReparse(importTag.Attributes),
      )
  ```

  `NewJSImportDeclaration` stores its arguments as they are
  (`ast_generated.go:2530-2537`). Its other callers are
  `UpdateImportDeclaration`, which takes replacement children and checks
  neither their presence nor their kinds (`ast_generated.go:2539-2551`),
  `Clone`, which passes the node's own children (`ast_generated.go:2564-2573`),
  and the decoder of nodes a client sends (`internal/api/encoder/decoder_generated.go:413-420`);
  by the paragraph above, no program file holds a node they build.
- **The tag.** `parseImportTag` (`internal/parser/jsdoc.go:940-954`) parses
  the clause, the specifier and the attributes with the functions the
  parse of kind 273 uses (`internal/parser/parser.go:2272-2277`):
  `tryParseImportClause`, nil or an import clause (`parser.go:2337-2347`);
  `parseModuleSpecifier` (`parser.go:2326-2335`), which returns
  `p.parseLiteralExpression(true)` on a string literal and otherwise
  `p.parseExpression()`; and `tryParseImportAttributes`, nil or an
  `ImportAttributes` node (`parser.go:2501-2509`, `3090-3114`). The
  specifier is never nil, a malformed tag included: `parseExpression`
  returns `parseAssignmentExpressionOrHigher`'s node (`parser.go:4058-4077`),
  whose last fallback is `parsePrimaryExpression`'s
  `return p.parseIdentifierWithDiagnostic(diagnostics.Expression_expected, nil)`
  (`parser.go:5606`), which reports the error and returns
  `p.createMissingIdentifier()` (`parser.go:5903`), an identifier of empty
  text (`parser.go:2981-2983`).
- **The reparse.** The node's clause, specifier and attributes are deep
  clones of the tag's: `DeepCloneReparse` (`internal/ast/deepclone.go:75-82`)
  returns nil for nil and otherwise the visitor's clone, each node rebuilt
  by its own kind's constructor (`deepclone.go:6-27`). Its modifiers are the
  clone of the tag's, and a JSDoc tag has none: `JSDocImportTag` holds
  `JSDocTagBase`, the clause, the specifier and the attributes
  (`ast_generated.go:7751-7756`).
- **The encoder.** Kinds 273 and 346 share one case of the child mask,
  `(boolToByte(n.ImportClause != nil) << 1) | (boolToByte(n.ModuleSpecifier != nil) << 2) | (boolToByte(n.Attributes != nil) << 3)`
  beside the modifiers' bit 0
  (`internal/api/encoder/encoder_generated.go:149-151`).
- **The client.** The client builds no node of kind 346 but a clone: the
  visitor table has no entry for it, so `visitEachChild` returns the node
  itself (`dist/ast/visitor.generated.js:45-50`), and `cloneNode` copies
  its four children (`dist/ast/factory.generated.js:447-453`, `531-533`).

So every node of kind 346 the client reads holds a specifier, produced as
kind 273's is, and a clause and attributes absent or produced as kind 273's
are: its children meet the contract the declaration of `ImportDeclaration`
states for kind 273's, on the same trust as that declaration. C3 checks the
shape's members on every node of kind 346 of the same corpus file, which
holds an `@import` of named bindings and one of a namespace with
attributes.

## Node lists

A source model array owns its store under `Array.prototype`
([arrays](SOURCE-MODEL.md#arrays)). A node list has its indices as getters
on its prototype, the class's fields as its own keys, and a prototype
overriding `at` and `Symbol.iterator`. The ordinary-array assumptions (own
keys, species, conversion) hold of ordinary arrays; node lists have their
own interpretation.

The package declares `interface NodeArray<T extends Node> extends
ReadonlyArray<T>, ReadonlyTextRange` with the members `hasTrailingComma?`
and a writable `transformFlags: number`. In a project with Node's types
(`tools/tsconfig.json` has `types: ["node"]`), `@types/node` merges
`interface ReadonlyArray<T> extends RelativeIndexable<T> {}`
(`compatibility/indexable.d.ts`) into the standard library's
`ReadonlyArray`, which is then no longer the library's alone and is read as
a plain interface: its overloads are refused as duplicate fields
(2026-10-17, 64 slices of `tools/`). Without the merge, an interface
extending a library array is refused. The reading below never reads
`NodeArray`'s heritage: `NodeArray<T>` is a host type of its own, so neither
`ReadonlyArray`'s declarations nor the merge into them are read for a node
list.

`NodeArray<T>` is the host type $`\mathsf{NodeList}(T)`$ with the provenance
key $`\kappa_{\mathit{RemoteNodeList}}`$, read as a readonly array of `T`
([below](#node-lists-in-the-model)): it admits the operations of a readonly
array, each member of the array overlay on a readonly receiver among them.
The audited rows, with $`n`$ the list's `length` at its creation and
$`v_0,\ldots,v_{n-1}`$ its elements:

| Operation                                                    | Result                                                                                                                         |
| ------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------ |
| `l.length`                                                   | $`n`$                                                                                                                          |
| `l[i]`, $`i`$ a number                                       | $`v_i`$ for an integer $`0\le i<n`$, else `undefined`                                                                          |
| `for (const x of l)`, `[...l]`                               | $`v_0,\ldots,v_{n-1}`$ in order                                                                                                |
| `l.some/every/find/findIndex/forEach/indexOf(…)`             | `Array.prototype`'s algorithm over $`v_0,\ldots,v_{n-1}`$, the callback called with $`(v_i, i, l)`$                            |
| `l.map/filter/flatMap/slice(…)`                              | a fresh ordinary array (`Array` species), built as from a dense array of the $`v_i`$                                           |
| `l.at(i)`                                                    | $`v_i`$ for an integer $`0\le i<n`$, else `undefined` (a non-integer index included), within the contract `T \| undefined`     |
| `l.pos`, `l.end`                                             | the list's start and end in its file's text, numbers fixed for the list's life                                                 |
| `l.transformFlags`, `l.hasTrailingComma`                     | `0` and `undefined`, within the contracts `number` and `boolean \| undefined`                                                  |

Each row is audited against `Array.prototype`'s algorithm on this receiver
([ECMA-262](REFERENCES.md#ecma-262)): `length` is an own data property the
package writes only in the constructor and the client cannot write;
`HasProperty` and `Get` of an index below $`n`$ reach a prototype getter
returning the memoized node; `ArraySpeciesCreate` reads `constructor`
(`RemoteNodeList`) and its `Symbol.species` (`Array`); a callback can
neither write the list (getters without setters) nor change $`n`$, so the
algorithm visits the indices it read at entry; a callback's exception
propagates out of the method; writes throw. The member rows read the
list's getters and fields, which nothing changes after its constructor. `"k" in l` is admitted as for
any object: the model answers it by `%HasProperty%`, a Boolean that narrows
nothing. Every other operation on a node list has the classification of
[the operation table](HOST-FAMILIES.md#operations-and-their-obligations),
and is refused when it has none.

### Node lists in the model

`NodeArray<T>` is read as `readonly T[]` with dense presence: a node list
has $`n`$ elements and no hole. A node list of the package enters the model as
an object of the external heap whose host classification T4 states, fixed
when it enters: the classification is an assumption about the package's
values, not a fact the pipeline establishes. The model's value is an ordinary dense
readonly array of the $`v_i`$, under `Array.prototype`'s contract, so the
operations of the table are the existing readonly-array rules, `l[i]` at a
`number` key [`%ElementAt%`'s](PROGRAM-TYPING.md#reads-at-an-index-from-the-length)
among them, and
`Array.isArray` gives `true` as it does at run time. A node list is a
restricted value ([restricted values](HOST-FAMILIES.md#restricted-values)): every operation
on which its model would not hold of a node list is stuck on it and carries
an obligation excluding host values, which no type a node list can be held
at meets, `unknown`, readonly arrays and readonly records included.

The node list's own members are those `hostNodeListMembers`
(`tools/compiler-api.mts`) states, each with its reviewed declaration:
`NodeArray<T>` is the meet of the dense readonly array of `T` and the
record

```math
\{\mathsf{readonly}\ \mathit{pos}\colon \mathsf{number};\ \mathsf{readonly}\ \mathit{end}\colon \mathsf{number};\ \mathsf{readonly}\ \mathit{hasTrailingComma}\colon \mathsf{boolean} \mid \mathsf{undefined};\ \mathsf{readonly}\ \mathit{transformFlags}\colon \mathsf{number}\}
```

so the model's node list is the dense readonly array of the $`v_i`$ that
also owns these four keys, each holding its value for the list's life.
None is a key `Array.prototype` provides, so the array's own-key exclusions
(`constructor`, `toString`, `join`, `Symbol.toPrimitive`) still hold, and
every other member is `ArrayProto`'s; the members' record adds no element,
so the list's presence stays dense. Each member is a readonly view, so a
write to one is refused (R1), `transformFlags` included, which the package
declares writable (`invalid-compiler-api-node-list-flags-write`, run under
Node). `hasTrailingComma`, declared optional, is present on every list
holding `undefined`, so it is read as a required member at
`boolean | undefined`, and a node list is no value of the exact reading of
`{ readonly hasTrailingComma?: boolean }`, absent or a Boolean
(`invalid-compiler-api-node-list-trailing-comma`, run under Node). The
members are read as `compiler-api-node-list-members` and
`blocker-compiler-api-node-list-metadata` read them.

Each row of the table holds of a node list for the reasons above, which T4
states and C4 runs: lengths around 16 (where index getters move from the
prototype to the instance), numeric keys that are no index (`-1`, a
fraction, past the end, `NaN`, the infinities), reentrant callbacks and callbacks that throw,
repeated and interleaved iterators, and every listed `Array.prototype`
member. An indexed read writes the list's hidden cursor (`_cursorIndex`,
`_cursorNodeIndex`) and materializes nodes into `sourceFile.nodes`; the
model's read promises no effect, which holds of every transparent
operation. `at`, whose override gives `undefined` at a non-integer index,
meets its contract, `T | undefined`.

## Node methods and callbacks

`getText`, `getStart`, `getEnd`, `getFullStart`, `getWidth`,
`getFullWidth`, `getLeadingTriviaWidth`, `getFullText`, `getSourceFile`,
`getLineAndCharacterOfPosition` and `forEachChild` are read at their
declarations as
[host-relative methods](SOURCE-MODEL.md#method-members-are-host-relative),
under T3. None makes a server request, so none runs the API's retained
callbacks. Each but `forEachChild` runs no client code and changes no
stable member, and its hidden effects are observed by no transparent
operation (T4), so its call changes no location of the model, on normal
return or throw: the family description states each at the empty footprint
with `onThrow` (`footprints`, each with its reviewed text), and a callback
calling only them is within the empty footprint
(`compiler-api-node-method-effect`). `forEachChild`'s own steps change no
location of the model either, and the only client code it runs is its
visitors, so it is read at each closed footprint $`\varepsilon`$: both
visitors' types and its call at $`\varepsilon`$, on normal return
(`footprints`, kind `callbacks`; the mechanism of the array members'
callbacks, [native footprints](SOURCE-CONTRACTS.md#native-footprints)). A
callback calling it with a visitor within $`\varepsilon`$ is within
$`\varepsilon`$ (`compiler-api-visitor-effect`), and one whose visitor pops
an array it reads is within no footprint keeping array stores
(`invalid-compiler-api-visitor-effect`).

`forEachChild<T>(visitNode, visitList?)` takes two visitors, both the
client's functions: `visitNode` runs on each child node and `visitList`,
when given, on each child list (a $`\mathsf{NodeList}`$), in the package's
child order, stopping at the first truthy result, which it returns, else
`undefined`. A visitor may write the client's own storage and never a host
object; the traversal reads only the buffer, so the visited children are
fixed whatever the visitor does, and a node list's store never changes
(T4), so no visitor changes what a later visit is passed. The call's effect
on the caller's heap is its visitors'. The visitor runs synchronously, during the call; an exception it
throws propagates out of `forEachChild`, which then has no normal
completion, and nothing is carried onto that exceptional edge.

## The sync API

**Retained callbacks.** `new API(options)` with `options.fs` registers
client functions the instance keeps and calls during any later request of
that instance. The contract reads the constructor as: the instance retains
each `fs` callback, and every later request of the instance may call each
of them any number of times, synchronously, before it returns, with string
arguments. The callbacks' types are their declared ones
(`readFile: (path: string) => string | null | undefined`, …), checked as the
client's functions like any other. A host request is an ordinary call: it
discards the caller's facts about the heap, which accounts for whatever the
callbacks write of the client's state. A callback that throws, re-enters the
API, or returns outside its type makes the request throw and leaves the
instance throwing on every later request; a throw is an allowed outcome.

**Requests' footprint.** A method a view lists whose arguments are
primitives and host objects is read at the footprint
$`\{\mathit{value}{:}\,\mathsf{any},\ \mathit{store}{:}\,\mathsf{grow}\}`$
on normal return where its view entry explicitly marks `request`
(`requestReading`): the client sends the
primitives and the host objects' ids, so the serialization with
`JSON.stringify` runs no code of the program (audited, `api.js`); the call
changes no location of the model but through its instance's retained
callbacks and the client's `JSON.stringify` of what they return, which
runs a `toJSON` the result holds (T6), the host's
own state is observed by no transparent operation (T4), and every instance
a verified program meets is opened with callbacks within that footprint,
their results' serialization included
(`invalid-compiler-api-callback-tojson`, whose callback's result pops an
array under Node). A
verified program opens none: `new API(…)` is outside the admitted language
(no view lists the constructor, reading rule 4;
`invalid-compiler-api-retained-fs`, whose retained
callback pops an array under Node). The front end's instances are opened by
`openCompiler` (`tools/compiler-channel.mts`), with `compilerFileSystem`'s
callbacks (`tools/files.mts`) or `tools/unchecked.mts`'s, which read files,
record answers in fresh or owned maps and write module cells, removing no
element of a store they did not allocate, and return strings, Booleans and
fresh lists of names, JSON values (audited). An instance a verified
program receives from outside is an input, whose callbacks within the
footprint are an assumption of T8. A `map` callback calling a request gives
a dense result (`compiler-api-request-effect`). No bound holds on a throw.
The methods whose arguments may hold an object of the program
(`API.parseConfigFile`, `API.updateSnapshot`, `Snapshot.getDefaultProjectForFile`,
`Program.getSourceFile`, `Program.getDeclarationDiagnostics`,
`Program.getSemanticDiagnostics`, `Program.getSyntacticDiagnostics`,
`Checker.resolveName`) put it into the payload, whose serialization runs
its `toJSON`; each is read at its declared signature, which states no
effect (`invalid-compiler-api-request-tojson`, whose `toJSON` pops the
mapped array under Node).

**Lifetimes.** The guarantee is type safety without source correspondence:
a request returns a value of its declared type or throws, whatever
snapshot, project or instance the handles it receives came from. That a
result describes the node passed is outside what verification states, as is
the front end's own correspondence with the source. The front end keeps one
compiler instance per purpose and compares trees across instances by text
and spans (`declaration-graph.mts`).

**Views.** `API`, `Snapshot`, `Project`, `Program`, `Checker`, `Symbol`,
`Type`, `Signature`, `NodeHandle`, `ThisTypePredicate` and
`AssertsThisTypePredicate` are host types read through their named views,
under T6.

### Audits of sync members

Cited: TypeScript 7.0.2, `dist/api/sync/api.d.ts` and
`dist/api/sync/api.js` of the installation bound by C0, audited 2026-10-25
(the last ten rows 2026-10-29).
Each declaration below is the exact text stored in `hostViews`; `tests/compiler-api.mts` checks
it against the installed declaration. The implementation audit supports T6,
an assumption about runtime behaviour, rather than a Lean proof.

| View member and declaration | Implementation and contract |
| --- | --- |
| `Checker.getContextualType(node: Expression): Type \| undefined;` | `getContextualType` sends snapshot and project ids and `getNodeId(node)`; the response becomes a cached host `Type` or `undefined`. Serialization contains no client object. The request reading gives the store-growth footprint on normal return under the retained-callback assumptions of T6 and T8. |
| `API.parseConfigFile(file: DocumentIdentifier): ConfigResponse;` | `parseConfigFile` initializes the channel and sends `{ file }` directly to `apiRequest`. An object identifier can run getters or `toJSON` during payload serialization, so its view entry retains the ordinary declared signature with no preservation guarantee. The response is the channel's JSON-decoded object; its fields are ordinary writable data. |
| `Snapshot.getProjects(): readonly Project[];` | `getProjects` checks disposal and returns `[...this.projectMap.values()]`, a fresh dense array of the snapshot's projects. It invokes no client callback and changes no existing model location. A disposed snapshot throws. |
| `Snapshot.dispose(): void;` | `dispose` marks the snapshot disposed, disposes its projects, clears its maps and registry, calls the internal `onDispose` closure created by `API.updateSnapshot`, then requests `release` with the snapshot id. The closure removes the snapshot and releases cache references; it is not supplied by the client. Retained filesystem callbacks, if requested by the channel, remain subject to T6 and T8. Repeated disposal returns immediately; subsequent operations may throw. The normal-return footprint permits growth and preserves existing stable members. |
| `Symbol.checkFlags: number` (declaration `readonly checkFlags: number;`) | The `Symbol` constructor assigns `data.checkFlags` once. No other assignment to `checkFlags` occurs in `api.js`. The member is a stable readonly number, with its value supplied by the server under T6. |
| `Project.rootFiles` (declaration `readonly rootFiles: readonly string[];`) | The `Project` constructor assigns `data.rootFiles`, the channel's JSON-decoded array, once; no other assignment occurs in `api.js`, and the package writes no element of it. The member is a stable readonly view of a dense array of strings under T6; a write through another alias is T8's. |
| `Program.getDeclarationDiagnostics(file?: DocumentIdentifier): readonly Diagnostic[];` | Sends snapshot and project ids and `file`, as `getSemanticDiagnostics` does, and returns the decoded array or a fresh empty one. An object identifier is serialized with `JSON.stringify`, so its view entry retains the declared signature. |
| `Program.getGlobalDiagnostics(): readonly Diagnostic[];` | Sends snapshot and project ids alone and returns the decoded array or a fresh empty one: a request, at the store-growth footprint on normal return (T6, T8). |
| `Checker.getSymbolAtLocation(nodes: readonly Node[]): (Symbol \| undefined)[];` | The method's second overload, beside `getSymbolAtLocation(node: Node)`. `Array.isArray` selects it, and `nodes.map(node => getNodeId(node))` reads the argument; the call runs no code of the program under the [trust surface](DESIGN.md#trust-surface)'s rows on arrays a program receives: a plain array, no proxy, owning no key `ArrayProto` declares (so `map` is the standard one) and no `constructor` (so `map` allocates an ordinary array), and holding data properties at its numeric keys (so `map` runs no getter). Outside those rows, a proxy, an array subclass or an indexed getter runs code during the call. `getNodeId` tests `instanceof RemoteNode` and reads the node's id, throwing on any other value; a hole, which `map` skips, is sent as `null`, and the server's answer, observed under Node, is an error (`invalid node handle`). It sends `getSymbolsAtLocations` with the ids and returns `data.map(…)` over the decoded response: a fresh dense array, one entry per node, each the client's shared `Symbol` for its id (the one the single form returns for that node) or `undefined` where the node has none (a statement, `invalid-compiler-api-array-query-entry`, run under Node). A request at the store-growth footprint on normal return (T6, T8), whose array result is fresh (`fresh` in `hostViews`). |
| `Checker.getTypeAtLocation(nodes: readonly Node[]): (Type \| undefined)[];` | As the row above, with `getTypeAtLocations` and the client's shared `Type`s: a request at the store-growth footprint whose array result is fresh. |
| `Signature.declaration` (declaration `readonly declaration?: NodeHandle \| undefined;`) | The `Signature` constructor assigns it, a new `NodeHandle` of the response's handle or `undefined`, and `api.js` assigns it nowhere else. It is an own writable, configurable data property, and the client shares one `Signature` per id (`getOrCreateSignature`), so code holding another alias may reassign it: each read is of `NodeHandle \| undefined`, and a test of it holds until the next call (`invalid-compiler-api-signature-declaration-call`, whose callback reassigns it through a signature fetched again, run under Node). The program writes it through no alias, the view's members being readonly; that what external code writes there is a `NodeHandle` or `undefined` is T8's. A signature with no declaration exists: the one TypeScript resolves at a binary expression (`invalid-compiler-api-signature-declaration`, run under Node). |
| `Symbol.getMembers(): ReadonlyMap<__String, Symbol>;` | `getMembers` returns `this.membersCache ??= this.fetchSymbolTable("getMembersOfSymbol")`. `fetchSymbolTable` asks the symbols' registry for the symbols (`fetchSymbols`, which sends the snapshot id, the symbol's canonical project id and its own id, primitives alone, and returns `[]` where the response is `null`), then fills a `new Map()` with `table.set(symbol.escapedName, symbol)` for each: the escaped name, a string of the response, as the key, and the registry's shared `Symbol` for its id as the value. A symbol with no members gives an empty `Map`, never `undefined`. The first call makes the request; every later call on the symbol, and on every alias of it (the registry keeps one `Symbol` per id), returns the same `Map`, which the package writes no more. So the result is shared, not fresh: the `Map` and the private field holding it are writable at run time by code holding the symbol, as the registry's own `Map` of symbols by id is, from which every request returning a symbol takes its answer (`getOrCreateSymbol`); a value written there is what a later call or request returns (C7). No check of the program can establish that a value is the package's `Symbol`: `instanceof` is admitted only at a class of the file ([operations](HOST-FAMILIES.md#operations-and-their-obligations)), and at the package's class it would answer `true` of an object other code builds on the class's prototype. What such code writes there being a `Map` of strings to the registry's symbols, as what it writes into the registry being its symbols, is T8's. The view reads it at `ReadonlyMap<string, Symbol>` (reading rule 5), whose members are `Map.prototype`'s, a request at the store-growth footprint on normal return (T6, T8). The keys are escaped names, `___x` for a member `__x`: `get` at a display name may find nothing (`invalid-compiler-api-symbol-table-get`, run under Node). C7 checks the implementation and the table. |
| `Symbol.getExports(): ReadonlyMap<__String, Symbol>;` | As the row above, with `exportsCache` and `getExportsOfSymbol`: a class's statics and its `prototype`, a module's exports. |
| `TypePredicateKind` (`dist/enums/typePredicateKind.enum.d.ts`) | A host enum of four members, `This` 0, `Identifier` 1, `AssertsThis` 2 and `AssertsIdentifier` 3, whose runtime object is the emitted enum of those values (C1). `getTypePredicateOfSignature` sends the snapshot, project and signature ids and builds a fresh record from the response: `kind`, `parameterIndex` and `parameterName` copied from it, `type` the registry's `Type` or `undefined`. The server's `kind` is the checker's `TypePredicateKind`, whose values the enum file is generated from (`internal/checker/types.go`); C7 meets each member at a predicate of its form. |
| `ThisTypePredicate`, `AssertsThisTypePredicate` | Their declarations state `parameterIndex: undefined`, but the client copies the server's index, 0 for a predicate about `this` (C7): a test of the index tells no predicate about a parameter from one about `this`, whose `parameterName` is `undefined` (`invalid-compiler-api-type-predicate-this-index`, run under Node). Their views list `kind`, `parameterName` and `type` and no index, so the index is read only where a test of `kind` has left the predicates about a parameter, as `collectDeclarations` reads it ([the repair](SOURCE-REWRITES.md#a-predicates-index-read-before-its-kind-is-tested)). An asserted predicate may state no type (`asserts x`; `invalid-compiler-api-type-predicate-type`, run under Node). |

### Stated type guards

The sync API's predicates over `Type` test bits of `flags` and
`objectFlags`, so they are no kind tests. A **stated type guard** is one
whose promise the contract states (`statedGuards`, T7), for each predicate a
unit narrows by: `isUnionType`, `isIntersectionType`, `isStringLiteralType`,
`isNumberLiteralType`, `isBigIntLiteralType`, `isBooleanLiteralType` and
`isTypeReference`. Each is read at its declaration in
`dist/api/sync/api.d.ts`, whose text the entry states,
`isUnionType(type: Type): type is UnionType` among them, as a
[user-defined guard](SOURCE-ELABORATION.md#user-defined-guards) is: its plain
signature and its promise signature about its argument, both at the empty
footprint. A call's `true` edge narrows an immutable binding argument to the
promised interface, read as declared: `UnionType` is `Type`'s view with
`getTypes(): readonly Type[]`, `StringLiteralType` the view with
`getFreshType`, `getRegularType` and `value: string`. The `false` edge keeps
the argument's type. Every other predicate of the package is read without its
promise ([guard recognition](HOST-FAMILIES.md#guard-recognition),
`invalid-compiler-api-sync-guard`).

Cited: TypeScript 7.0.2, `dist/api/sync/api.js`, audited 2026-10-29. Each
stated guard's implementation is the entry's text, which
`tests/compiler-api.mts` compares with the function Node loads: it reads
`type.flags`, and `isTypeReference` through `isObjectType` also
`type.objectFlags`, and the enum objects C1 checks. On a `TypeObject`, the
only class whose values have a host type reaching `Type`
([host provenance](#host-provenance)), these are own data fields its
constructor assigns, and its prototype defines no getter, so a call runs no
code of the program, makes no request, writes nothing and throws nothing.
The promised members are `TypeObject`'s prototype methods and own data
fields: `getTypes` calls `fetchTypes` without handles, requesting the
constituents on every call and returning a fresh dense array of
registry-shared type objects. `getTarget` calls `fetchType` with the target
handle, returning its registered object when cached and requesting it when
uncached. `getFreshType` and `getRegularType` likewise use `fetchType` with
their respective handles, returning a freshable type or `undefined` when
there is no handle. `value` is the decoded literal, and `objectFlags` is an
own numeric data field. These methods may make requests; the empty footprint
stated above belongs to the predicates. That each holds
its declared type where the guard answers `true` is T7, observed by
`tests/compiler-api.mts` on literal, union, intersection and reference
types.

`Type`'s `this is X` methods (`type.isUnionType()`) are no members of its
view: their promise is about the receiver, which is no actual of a call.
Each calls the predicate of its name on its receiver (`api.js`), so the front
end calls the predicate instead
([constructs avoided](SOURCE-REWRITES.md#a-this-is-x-method-of-the-compilers-type),
`invalid-compiler-api-type-method`). A parameter typed by a sub-interface
(`getTypeArguments(type: TypeReference)`) is read as declared; the client
meets it after the stated guard.

## Namespace imports and bitwise operators

`import * as ns from M`, where every occurrence of `ns` is a member read
`ns.x` or a qualified type name `ns.T`, reads each member as a binding of its
own, the export the checker binds it to, at its own span: a module namespace
object's members are immutable bindings
([ECMA-262](REFERENCES.md#ecma-262)). Any other use of `ns` and a write of a
member are refused, and
so is a call `ns.f(…)` of a member whose signatures state a `this`
parameter, since the call passes the namespace object as the receiver
(`namespace-import` in
[derived source forms](SOURCE-ELABORATION.md#derived-source-forms)).

`a & b`, `a | b`, `a ^ b`, `~a`, `a << b`, `a >> b` and `a >>> b` with
operands of type `number` evaluate `ToInt32` or `ToUint32` of numbers, run
no client code and give a `number`; operands that may be objects are
refused, and so are bigints but for `^`, which also takes two bigint
operands, and `~`, which also takes one: the calculus's `xor` states both. A flag test `(t.flags & TypeFlags.Union) !== 0`
is arithmetic on numbers and a comparison. The operators are the calculus's
binary operators, with their step rule and the one typing rule `arith`
([judgments](PROGRAM-TYPING.md#judgments-and-constructor-views)).

## Binding the contract to the implementation

A fast suite of `test-all.sh`, `tests/compiler-api.mts`, needs no build. It
binds the contract to the implementation it was reviewed against and
re-runs the measurements of [the package at run time](#the-package-at-run-time)
as regression evidence.

- **C0, binding.** The installed package has the reviewed name, version
  and declaration digest. A lookalike package elsewhere is outside the
  contract. The AST guard table binds its entry point and static dependency
  closure by content through the
  [guard closure](HOST-FAMILIES.md#the-guard-table). C6 and C7 compare the
  sync implementations they name with their reviewed texts. These are the
  executable binding checks; the declaration digest alone states no fact
  about a sync implementation or a server executable.

  General `new API`, `API.fromLSPConnection` and caller-selected backends
  are refused by the named views. An instance supplied to verified code
  satisfies T6 and T8, including the selected backend and retained-callback
  assumptions. Construction of that incoming instance is outside the
  certified client.

- **C1, enums.** For every enum the contract reads (`hostEnums`), every
  member of its `.enum.d.ts` is an integer literal, and the runtime object
  Node loads for `#enums/<name>` under the `default` condition matches the
  declaration by `enumObjectMatches` ([enums](SOURCE-CONTRACTS.md#enums));
  the entry points exporting the enum export that object. The object is
  mutable; that it is never written is F5.
- **C2, guards (regression evidence).** The
  [guard table](HOST-FAMILIES.md#the-guard-table)'s generator, run on every
  exported guard, gives exactly the reviewed table, its unlisted exports
  exactly those outside the recognition contract; every entry run under
  Node on an object of each kind (and on every number in a range around
  $`\mathcal K`$ for a tag guard) answers exactly its tag set, and every
  node guard, whose behaviour on `undefined` the description admits, throws
  a `TypeError` there.
- **C3, shapes (regression evidence).** `make compiler-api-shapes`
  (`tests/compiler-api-shapes.mts`, about 20 s) reads the family table over
  the installed declarations and walks every node of `tools/*.mts`,
  `pipeline/*.mts`, `tests/*.mts`, `dev/*.mts`, `pipeline/examples/*.ts` and
  `tests/node-shapes-corpus/` (TypeScript, JSX and JavaScript with JSDoc),
  each node's JSDoc included: it fails on a property a kind's flattened
  shape states required, not admitting `undefined` (inherited and generic
  components included), that a node of that kind lacks and no correction
  covers, and, for an [audited shape](#audited-shapes), on a member outside
  its declared type or one no node holds. Beyond audited shapes, it checks the presence of every checked required property, not
  required methods, member types, children's kinds or stability: presence
  regression evidence, not a completeness proof, and its coverage is the
  corpus's, so a member absent only in a form the corpus does not contain
  is not found. It reports the kinds the corpus never reaches and the
  members of reached kinds no node holds. On 2026-10-19 it reaches 268 of
  352 kinds; of the 84 others, 80 state no checked property beyond the
  root's and `NodeBase`'s, which every reached node is checked for (trivia,
  punctuation and keyword tokens, which `forEachChild` does not visit,
  `NotEmittedStatement`, `NotEmittedTypeElement` and `Count`), and 4 state
  their own: `SyntaxList` (`children`), which only `getChildren` builds,
  and `SyntheticExpression`, `PartiallyEmittedExpression` and
  `SyntheticReferenceExpression`, which the checker and the emitter make
  and no parse gives.
- **C4, members, lists and operations (regression evidence).** On the
  corpus (C3's walk), every property member of every node's shape,
  required or optional, is read twice and again after the entry point's
  token functions have run over its file, each giving one value, a member
  no prototype getter backs being `parent` or one of a reviewed list; the
  omitted ones are the contract's list, `jsDoc` giving two arrays to two
  reads and `tokenCache` absent, then a `Map` after `getTokenAtPosition`.
  For node lists of lengths 0, 1, 15, 16, 17 and 32, each transparent
  operation of the operation table runs, with callbacks that record their
  arguments and their `this`, and each member `hostNodeListMembers` states,
  declared as reviewed by its owner, is backed as stated (a prototype getter
  without setter, or an own data property at 0 or `undefined`) and gives
  the value it gave at the start; no JavaScript file of the package names
  `transformFlags` or `hasTrailingComma` outside `RemoteNodeList`:
  - each row of the node-list table, and `Set`, `f.apply`, argument
    spread, and array destructuring with and without a rest;
  - a callback throwing at each index, a `map` callback throwing at each
    index, and an iteration left by `break`, by `return`
    and by a destructuring with fewer targets than elements, each closing
    the iterator after partial consumption and followed by a fresh
    iteration and by indexed reads;
  - reentrancy: a callback running every row on the same list (an indexed
    read, a nested `map`, a nested iteration);
  - interleaving: two iterators of one list advanced alternately, with
    indexed reads and `length` between their steps;
  - hidden state: after each sequence, every row gives the answers it gives
    on a fresh list of the same nodes, and the nodes are the same objects.

  For every exported function of the package, its own keys and their
  descriptors are those T4 states, and `typeof` of every host object and
  node list met is `"object"`.
- **C6, stated guards.** Each [stated guard](#stated-type-guards) is
  declared as its entry states, and the function Node loads for it, and
  for `isTypeReference`'s helper `isObjectType`, is the entry's reviewed
  text; a checker type has own data descriptors for `flags` and
  `objectFlags` (`flags` numeric, `objectFlags` numeric on object types),
  and its prototype defines no accessor; and on
  literal, union, intersection and reference types of a small program each
  guard answering `true` leaves the members its promise covers at their
  declared types: `getTypes` gives fresh arrays with an own element at every
  index, literal types have `value`, `getFreshType` and `getRegularType`
  (including the returned freshable types), and references have `objectFlags`
  and `getTarget` (regression evidence for T7).
- **C7, symbol tables and type predicates.** The methods Node loads for
  `Symbol.getMembers`, `getExports` and `fetchSymbolTable`, the registry's
  `fetchSymbols` and `Checker.getTypePredicateOfSignature` are the texts
  `auditedSyncMethods` states. On a small program's class and functions,
  each table is a native `Map` owning no key, the same `Map` at every call
  on its symbol, each key a string equal to its value's escaped name, each
  value the registry's `Symbol` the checker gives at the member, and the
  table of a symbol with no members empty; each predicate's `kind` is the
  `TypePredicateKind` member of its form, all four met, its
  `parameterName` a string exactly for a predicate about a parameter, its
  `parameterIndex` a number, 0 for one about `this`, and its `type` absent
  exactly for `asserts` with no `is`; and a write through another holder of
  a table, of the field caching it or of the registry's map of symbols
  changes what a later call or request returns (regression evidence for the
  [audits](#audits-of-sync-members)).
- **Declaration texts.** Each contract entry's reviewed text is compared
  with the installed declaration, as `library-globals.mts` does.

## Trust

Each sentence is an assumption the verification result is relative to. None
is proved. C0 states the executable binding scope; the other checks give
regression evidence for the named properties, not proofs of the assumptions.

- **T1 (node invariant).** F1 and F2 of the
  [family rows](HOST-FAMILIES.md#trust-rows) for this description: every
  object whose prototype chain carries $`\kappa_{\mathit{RemoteNode}}`$ has a
  `kind` in $`\mathcal K`$, the members $`S_k`$ states for it, and the
  marker `"RemoteNode"` under `[[host]]` in its model value; its stable
  members, required and optional, keep their values for its life. For
  `JSTypeAliasDeclaration` (345), which no declaration states,
  $`S_{345}`$ is its [audited shape](#audited-shapes): `TypeAliasDeclaration`'s
  `name`, `typeParameters` (absent, or a dense readonly node list of
  `TypeParameterDeclaration`) and `type` at kind 345, with the members of
  `DeclarationBase`, `StatementBase` and `ModifiersBase`; the review of the
  package's getters states it, and C3 is its regression evidence.
- **T1′ (marker to invariant).** F1′ for the marker `"RemoteNode"`.
- **T2 (guards).** F3 and F5 for the description's guard table.
- **T3 (node methods).** The node methods make no server request, run no
  client code but `forEachChild`'s visitors, which they call synchronously,
  only with children of the receiver, in a fixed order, and propagate a
  visitor's exception; they change no stable member; they return values of
  their declared types or throw. With T4, a call of one but `forEachChild`
  changes no location of the model, on normal return or throw, and a call
  of `forEachChild` changes none but through its visitors, which the family
  description states (`footprints`).
- **T4 (restricted values).** A host object behaves as the record of its
  stated members and a node list as the dense readonly array of its
  elements owning its stated members (`hostNodeListMembers`) under every
  transparent operation of
  [the operation table](HOST-FAMILIES.md#operations-and-their-obligations), and this
  relation is preserved by every sequence of them, interleaved with client
  code, through any number of aliases, inside callbacks the operations run
  (reentrant ones included) and across an exceptional exit from a callback
  or an iteration: each operation gives the result the model gives, runs
  only the client code the model runs, with the same arguments in the same
  order, and propagates the same exception; its hidden effects (a node
  list's cursor fields, `sourceFile.nodes`, a memoized node) are observed
  by no transparent operation. Each host object corresponds to a
  host-classified model object owning its stated members and its runtime
  object's undeclared own data fields, with model prototype objects owning
  the keys its runtime chain provides beyond those, so `in` and
  `%HasProperty%` answer as at run time; a node list's also owns its store
  of the $`v_i`$; a transparent library entry's contract holds of these as
  of any value of its parameter types. Host values are objects, not callable,
  `typeof` gives `"object"` for them, and `Array.isArray` gives `true`
  exactly for node lists. Node lists are the only array-like host values;
  their length, elements and stated members never change: `pos` and `end`
  are getters reading the list's buffer, and `transformFlags` and
  `hasTrailingComma` own data properties holding 0 and `undefined`, which
  no code writes. A node list's iterator is a
  generator, which keeps its position in its own state: closing it (its
  `return`, called by a `break`, a destructuring or a throwing callback)
  runs no observable cleanup and leaves the list's relation to its model
  intact. The package's exported functions are ordinary function objects,
  with own keys `length`, `name` and, for a function declaration,
  `prototype`, none enumerable.
- **T5 (enum objects).** The enum objects Node loads for the package's
  `#enums/*` imports that the contract reads hold exactly the member values
  their declarations state. (`CharacterCodes` does not: `ogham`; the
  contract does not read it.)
- **T6 (sync API).** Each member of a host view, called with the receiver
  and arguments of its declared types, makes its request, during which it
  may call the instance's retained `fs` callbacks synchronously with string
  arguments, serializing what each returns with `JSON.stringify`, and then
  returns a value of its declared type or throws; it
  runs no other client code but what serializing its payload runs of the
  program's objects among its arguments (their `toJSON` methods and
  getters) and what serializing the callbacks' results runs (their
  `toJSON` methods), and changes no stable member of an object it returned earlier.
  With T4 and callbacks within
  $`\{\mathit{value}{:}\,\mathsf{any},\ \mathit{store}{:}\,\mathsf{grow}\}`$,
  a call of a member whose arguments are primitives and host objects is
  within that footprint on normal return. A result need not describe the handles passed when they
  come from another snapshot, project or instance.
- **T7 (stated type guards).** For each stated guard $`g`$ promising
  $`X`$ ([stated type guards](#stated-type-guards)): when $`g`$ returns
  `true` on a value of a host type, the members $`X`$ adds over `Type` return
  values of their declared types.
- **T8 (external code).** Every value code outside the linked certified closure
  gives a certified function or closure meets the classified
  interpretation recursively, and every sync API instance it gives was
  opened with `fs` callbacks that, with the serialization of their
  results, stay within
  $`\{\mathit{value}{:}\,\mathsf{any},\ \mathit{store}{:}\,\mathsf{grow}\}`$:
  its arguments, the results of external
  functions it calls, the arguments external code passes to its callbacks,
  and every location reachable from them hold no host object where their
  contract excludes one. An external callable's contract respects the
  operations' obligations: no external declaration gives an obligated
  library value (`Object.values` under another name) at an ordinary function
  type. For the front end, the external entries are the package's modules
  (`typescript/unstable/ast`, `typescript/unstable/sync`, under T1, T3 and
  T6); the members of `node:fs`, `node:path`, `node:crypto` and
  `node:module` the front end imports, of which the
  [library modules](SOURCE-CONTRACTS.md#library-modules) audit only the
  listed overloads (`execFileSync`, `writeFileSync`), every other one an
  assumption of this clause needing its own review; and the front end's own
  functions not yet verified, which call verified ones, for each of which
  the clause is an assumption until it, its initialization and its
  dependencies are in the linked certified closure. What such code writes
  into the package's objects it holds keeps their views' types: a
  `Signature`'s `declaration` a `NodeHandle` or `undefined`, a symbol's
  member and export tables and the private fields caching them a `Map` of
  strings to the registry's symbols, the registry's map of symbols by id
  the symbols of those ids. Inside that closure a
  call or a return is an internal edge, whose classified values the checking
  of both sides gives; the clause stays on external callers and callbacks,
  uncertified imports, native results and the storage they reach, and the
  environment the closure captures.

## Restrictions

Behaviours excluded because soundness needs it:

|     | Restriction                                                                       | Behaviour it excludes                                                                                                                                                            |
| --- | --------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| R1  | No client write to a member of a host type                                        | Mutating compiler objects: `list.transformFlags = 1`, `sourceFile.tokenCache = …`, `list.length = 0`, writes through any writable declared member or structural alias            |
| R2  | No client value meets a host type; host values come only from the package, and no value of its node builders (`hostNodeBuilders`: the factory, the clones, the visitors) is read | Passing a forged node, type or symbol to the API (an object literal, a spread or `Object.assign` copy of a node, a class implementing `ts.Node`); a node the factory, a clone or a visitor builds, whose root lacks `parent` (`invalid-compiler-api-node-factory`, `invalid-compiler-api-node-clone`, `invalid-compiler-api-node-jsdoc-visitor`, `invalid-compiler-api-node-jsdoc-visitor-namespace`, `invalid-compiler-api-node-jsdoc-visitor-reexport`, run under Node; the handwritten visitors are refused through subpath imports, AST namespace imports and program re-exports) |
| R3  | A host guard narrows to what its implementation accepts                           | Relying on `isTypeAliasDeclaration`, `isImportDeclaration`, `isAnyImportSyntax` excluding JavaScript kinds (`invalid-compiler-api-js-alias`); relying on `isExpression` matching the declarations' category |
| R4  | A host enum type at a package position is `number`                                | Exhaustive reasoning over flag values (`switch (node.flags)` with a case per member and no default)                                                                              |
| R5  | Bitwise operators take `number` operands only, but `^`, which also takes two bigint operands, and `~`, which also takes one | `obj & 1` (runs `valueOf`), `1n & x`                                                                                                                  |
| R6  | An abstract node type is the union of the shapes below it, with brands optional   | Using a brand member as evidence (`"_expressionBrand" in n`)                                                                                                                     |
| R7  | Every admitted `API` instance runs the executable the package selects             | `new API({ tsserverPath })`, `pipe` options, `API.fromLSPConnection`                                                                                                             |
| R8  | An object spread, an object pattern's rest, `Object.assign`, `Object.values`, `Object.entries` and `Object.getOwnPropertyDescriptor` need operand types that exclude host values | `{ ...node }`, `const { kind, ...rest } = node`, `Object.assign({}, node)`, `Object.values(list)`, `Object.getOwnPropertyDescriptor(list, "_cursorIndex")`, through `unknown`, readonly records, `Array.isArray`, type parameters and callbacks |

Limits of the mechanism, each a scoped refusal of behaviour that is safe in
JavaScript and could be admitted with more machinery:

|     | Limit                                                                   | What it refuses                                                     |
| --- | ----------------------------------------------------------------------- | ------------------------------------------------------------------- |
| L1  | A guard outside the accepted syntax is refused at its use               | `isLeftHandSideExpression`, `isUnaryExpression` as narrowings       |
| L3  | A namespace import is used only through member reads and qualified type names, each member one binding; a member stating a `this` parameter is not called through it | `const m = ts`, `ts[name]`, passing `ts`, `ts.f()` for `f(this: X)` |
| L4  | A member whose reads give no one value for a node's life is refused at its read; one that allocates could be stated as a host operation returning a fresh array | Reading `node.jsDoc`, `sourceFile.tokenCache`  |
| L5  | A host parameter of a branded type is refused; an opaque primitive type would admit the package's own values | Passing a `Path` back to `getSourceFileMetadataByPath` |
| L6  | A host class member outside its named view is refused at its use        | Calling a `Checker` method the view does not list                   |
| L7  | A merge's accumulator needs a type excluding host values, which a fresh copy's type states only through a field, a closed bound or an index | A spread after a spread of a value whose copy states none (`{ ...c, n: 1 }` with `c` holding only private fields); a key-adding write on a local annotated by optional fields alone (`const o: { a?: number } = {}; o.a = 3`) |

Under R3, the true edge of `isTypeAliasDeclaration` holds both kinds, so it
reads the members both shapes state (`blocker-type-alias-guard-member`) and
does not establish `TypeAliasDeclaration` itself; so does the true edge of
`isImportDeclaration`, which holds `JSImportDeclaration` beside
`ImportDeclaration` (`blocker-let-guard-import-specifier` reads
`moduleSpecifier`, `invalid-compiler-api-js-import-guard` is refused where
it returns the node's kind as `ImportDeclaration`'s). The kind test
(`n.kind === SyntaxKind.TypeAliasDeclaration`) narrows exactly; on a
JavaScript file the guard accepts `JSTypeAliasDeclaration` and the kind test
rejects it. The front end reads TypeScript files only: its parser refuses a
file no strict `tsconfig.json` claims, and declarations come from `.ts` and
`.d.ts` files. So replacing such a guard by its kind test changes no input it
accepts, and the front end recognises a type alias by its kind
([the rewrite](SOURCE-REWRITES.md#a-type-alias-recognised-by-a-guard-accepting-a-jsdoc-typedef)).

## Tests

`make cases P=compiler-api` runs the pipeline cases of this contract, each
described in [cases.mts](../pipeline/cases.mts): positive and negative
sources importing the package from `pipeline/compiler-api-project/`, the
negatives with their counterexample run under Node. The controls a source
cannot make (forged claims and evidence, a family description of another
digest, the string-tagged stand-in) are in
[test.mts](../pipeline/test.mts); C0–C7 are `tests/compiler-api.mts`,
`tests/compiler-api-guards.mts` and `tests/compiler-api-shapes.mts`.

## Where it lives

- `tools/compiler-api.mts`: the host package's name and modules; the host
  types and their views; the corrections; the omitted members; the
  refused guards; the installation and digest of
  C0, in the family description. Each entry carries the declaration text
  reviewed, as in `library-globals.mts`.
- `tools/host-families.mts` and `compilerApiFamily` in
  `tools/compiler-api.mts`: the family description and its interpreter;
  `tools/family-activation.mts`: the active descriptions, each
  installation's resolution and digest check, and the guard tables'
  activation.
- `tools/declaration-graph.mts`: reading rules 1–5, the family's readings at
  the run's selection, host enums, method overloads in declared classes,
  private members skipped.
- `tools/fragment-*.mts`: `host-guard` over the guard table, the
  membership test `tagMember`, namespace imports, bitwise operators; the
  table's generator is a review aid, outside the front end; the table's
  activation, in `tools/family-activation.mts`, reads the package's modules with
  a compiler of its own.
- `tests/compiler-api.mts`: C0, C1, C4, C6 and C7 (the symbol tables and
  type predicates against `auditedSyncMethods`); `tests/compiler-api-guards.mts`:
  C2; `tests/compiler-api-shapes.mts`: C3.
