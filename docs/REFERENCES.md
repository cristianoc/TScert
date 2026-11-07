# References

Every paper, specification, tool and issue this development draws on, in one
place. Other documents cite an entry by a short link to its anchor, such as
[Abadi and Cardelli 1996](#abadi-and-cardelli-1996); they do not restate the
bibliography.

Each entry gives the full citation, what the project takes from the work, and
where that is discussed in the documents and code.

## Semantics and logical relations

### Appel and McAllester 2001

Andrew W. Appel and David McAllester. *An indexed model of recursive types for
foundational proof-carrying code.* ACM Transactions on Programming Languages
and Systems 23(5):657–683, 2001.
[doi:10.1145/504709.504712](https://doi.org/10.1145/504709.504712).

**Used for** the step-indexed model: a type is a family indexed by a budget,
`Safe A n` asks for safety only for $`n`$ steps, and a recursive type reads its
operands only at lower indices. This is the budget of `Safe`, `SafeGraph` and
every `Fam`.
**Discussed in** [SEMANTICS: computations and recursive types](SEMANTICS.md#computations-and-recursive-types),
[POSITIVE-TYPES: notation](POSITIVE-TYPES.md#positive-types),
[SOURCE-MODEL: heap and contracts](SOURCE-MODEL.md#heap-and-contracts).

### Ahmed 2004

Amal Ahmed. *Semantics of Types for Mutable State.* PhD thesis, Princeton
University, 2004.

**Used for** step-indexed worlds for higher-order mutable state: every
location carries a type (here, a contract) in a world, a reference is
invariant because the world fixes its contract, heap satisfaction ties
contracts to contents, and functions are safe in every future world. This is
`WorldT`, `recT`, `HeapOk` and admissible world extension.
**Discussed in** [SOURCE-MODEL: heap and contracts](SOURCE-MODEL.md#heap-and-contracts),
[SEMANTICS: computations and recursive types](SEMANTICS.md#computations-and-recursive-types).

### Nakano 2000

Hiroshi Nakano. *A modality for recursion.* Proceedings of the 15th Annual
IEEE Symposium on Logic in Computer Science (LICS 2000), pp. 255–266.
[doi:10.1109/LICS.2000.855774](https://doi.org/10.1109/LICS.2000.855774).

**Used for** guarded recursion: a recursive type is well defined when its
recursive occurrences sit under a guard (the later modality ▷), here a read
below the current budget.
**Discussed in** [SEMANTICS: computations and recursive types](SEMANTICS.md#computations-and-recursive-types),
[SOURCE-MODEL: heap and contracts](SOURCE-MODEL.md#heap-and-contracts).

### Birkedal et al. 2012

Lars Birkedal, Rasmus Ejlers Møgelberg, Jan Schwinghammer and Kristian
Støvring. *First steps in synthetic guarded domain theory: step-indexing in
the topos of trees.* Logical Methods in Computer Science 8(4:1), 2012;
conference version LICS 2011.
[doi:10.2168/LMCS-8(4:1)2012](https://doi.org/10.2168/LMCS-8%284:1%292012).

**Used for** the categorical reading of the guarded fixed point: contractive
operators on step-indexed families have unique fixed points, with no
monotonicity required, so recursion through function domains is admitted.
**Discussed in** [SEMANTICS: computations and recursive types](SEMANTICS.md#computations-and-recursive-types)
(`Tower.lean`).

### Banach 1922

Stefan Banach. *Sur les opérations dans les ensembles abstraits et leur
application aux équations intégrales.* Fundamenta Mathematicae 3:133–181,
1922.

**Used for** the fixed-point theorem behind recursive types: a contractive
operator, with distance the first budget at which two families disagree, has
a unique fixed point.
**Discussed in** [SEMANTICS: computations and recursive types](SEMANTICS.md#computations-and-recursive-types).

### Wright and Felleisen 1994

Andrew K. Wright and Matthias Felleisen. *A syntactic approach to type
soundness.* Information and Computation 115(1):38–94, 1994.
[doi:10.1006/inco.1994.1093](https://doi.org/10.1006/inco.1994.1093).

**Used for** the shape of the safety statement with exceptions: a well-typed
program yields a value of its type, takes a step, or raises; a type says what
a value is, never that none is thrown. The development proves this shape
semantically, not by progress and preservation.
**Discussed in** [DESIGN: principles](DESIGN.md#principles),
[SOURCE-MODEL: throws](SOURCE-MODEL.md#throws),
[SEMANTICS: computations and recursive types](SEMANTICS.md#computations-and-recursive-types).

### Reynolds 1983

John C. Reynolds. *Types, abstraction and parametric polymorphism.*
Information Processing 83, Proceedings of the IFIP 9th World Computer
Congress, pp. 513–523. North-Holland, 1983.

**Used for** the idea behind `Parametricity.accept_reassign`: a checker that
never inspects how a type parameter is interpreted accepts a generic body at
every interpretation, so one derivation covers every instantiation.
**Discussed in** [DESIGN: generic bodies](DESIGN.md#generic-bodies),
[DESIGN: lasting decisions](DESIGN.md#lasting-decisions),
[POSITIVE-TYPES: parameter and scheme rows](POSITIVE-TYPES.md#parameter-and-scheme-rows).

## Objects and self types

### Abadi and Cardelli 1996

Martín Abadi and Luca Cardelli. *A Theory of Objects.* Monographs in Computer
Science, Springer, 1996.
[doi:10.1007/978-1-4419-8598-9](https://doi.org/10.1007/978-1-4419-8598-9).

**Used for** self-application: in the ς-calculus a method is a function of
its host object (its self), and invoking `o.l` runs the method with `o` bound
to self. A method member's contract here is likewise relative to its host:
read from `o` and invoked with receiver `o` it behaves as typed, and it
promises nothing for another receiver (`methodT`, `holdsAt`, `bindMember`).
The development takes the self-application semantics, not the book's Self
types or its object subtyping.
**Discussed in** [SOURCE-MODEL: method members are host-relative](SOURCE-MODEL.md#method-members-are-host-relative),
[POSITIVE-TYPES: records](POSITIVE-TYPES.md#records) (`methodT`, uncited),
`lean/Verification/Types/MethodMembers.lean` (module comment).

### Smith, Walker and Morrisett 2000

Frederick Smith, David Walker and Greg Morrisett. *Alias Types.* In
Programming Languages and Systems (ESOP 2000), LNCS 1782, pages 366–381,
Springer, 2000.
[doi:10.1007/3-540-46425-5_24](https://doi.org/10.1007/3-540-46425-5_24).

**Used for** the strong update: a change to a location's type is sound where
no other reference to the location exists, since no one else holds the old
type. A key-adding write changes an object's own keys, so it is typed only on
a local's own fresh object nothing else has reached; the pipeline takes the
idea, not the paper's linear capabilities: the unaliasedness is a syntactic
fact of the source (`growSites`), and the write is a copy the local is
rebound to rather than an update in place.
**Discussed in** [SOURCE-MODEL: objects and prototypes](SOURCE-MODEL.md#objects-and-prototypes),
[PROGRAM-TYPING: key-adding writes](PROGRAM-TYPING.md#key-adding-writes).

## Type-system design

### Frisch, Castagna and Benzaken 2008

Alain Frisch, Giuseppe Castagna and Véronique Benzaken. *Semantic subtyping:
Dealing set-theoretically with function, union, intersection, and negation
types.* Journal of the ACM 55(4):19:1–19:64, 2008; conference version LICS
2002. [doi:10.1145/1391289.1391293](https://doi.org/10.1145/1391289.1391293).

**Used as the contrast** for subtyping in a model with state. The
set-theoretic arrow decomposition $`(A\to B)\wedge(A\to C)\le A\to(B\wedge C)`$
holds in semantic subtyping and fails here: an allocating function meets both
arrows by choosing different cell contracts. The development therefore keeps
a clause-to-clause rule and refuses that law.
**Discussed in** [SEMANTICS: a design constraint](SEMANTICS.md#a-design-constraint),
[DESIGN: lasting decisions](DESIGN.md#lasting-decisions).

### Amadio and Cardelli 1993

Roberto M. Amadio and Luca Cardelli. *Subtyping recursive types.* ACM
Transactions on Programming Languages and Systems 15(4):575–631, 1993.
[doi:10.1145/155183.155231](https://doi.org/10.1145/155183.155231).

**Used for** the coinductive treatment of recursive types: a sound and
complete axiomatization of equality and subtyping for recursive types, the
cycle handled by an assumption set (the Amber rule). Recursive types here are
finite graphs checked coinductively over a table of assumed pairs, and family
entries lift those pairs to pairs with parameters.
**Discussed in** [POSITIVE-TYPES: subtyping](POSITIVE-TYPES.md#subtyping),
[RECURSIVE-EQUATIONS: related work](RECURSIVE-EQUATIONS.md#7-related-work).

### Brandt and Henglein 1998

Michael Brandt and Fritz Henglein. *Coinductive axiomatization of recursive
type equality and subtyping.* Fundamenta Informaticae 33(4):309–338, 1998;
conference version TLCA 1997.

**Used for** the coinductive rule over an assumption set that the
certificate checker's table $`\Delta`$ follows.
**Discussed in** [POSITIVE-TYPES: notation](POSITIVE-TYPES.md#positive-types),
[RECURSIVE-EQUATIONS: related work](RECURSIVE-EQUATIONS.md#7-related-work).

### Solomon 1978

Marvin Solomon. *Type definitions with parameters.* In Proceedings of the 5th
ACM Symposium on Principles of Programming Languages (POPL), 31–38, 1978.
[doi:10.1145/512760.512765](https://doi.org/10.1145/512760.512765).

**Used for** the classification of generic declarations as parameterized
type definitions, and of the non-regular ones (such as `Promise`, whose
`catch` returns `Promise<T | R>`) as those that unfold to infinitely many
distinct subtrees. No finite table presents a non-regular definition, which
is why each declaration becomes one equation with symbolic applications.
**Discussed in** [RECURSIVE-EQUATIONS: the problem](RECURSIVE-EQUATIONS.md#1-the-problem),
[related work](RECURSIVE-EQUATIONS.md#7-related-work).

### Kennedy and Pierce 2007

Andrew J. Kennedy and Benjamin C. Pierce. *On decidability of nominal
subtyping with variance.* International Workshop on Foundations and
Developments of Object-Oriented Languages (FOOL/WOOD), 2007.

**Used for** the nearest known limit on relating expanding definitions:
nominal subtyping with variance is undecidable once inheritance is
expansive. The result concerns nominal inheritance; the structural
inclusion here is undecidable by a separate argument
([Friedman 1976](#friedman-1976)).
**Discussed in** [RECURSIVE-EQUATIONS: related work](RECURSIVE-EQUATIONS.md#7-related-work),
[family subtyping](RECURSIVE-EQUATIONS.md#4-subtyping).

### Abadi, Cardelli, Curien and Lévy 1991

Martín Abadi, Luca Cardelli, Pierre-Louis Curien and Jean-Jacques Lévy.
*Explicit substitutions.* Journal of Functional Programming 1(4):375–416,
1991. [doi:10.1017/S0956796800000186](https://doi.org/10.1017/S0956796800000186).

**Used as the contrast** for what an equation application delays. An
application is a closure (an equation paired with its arguments) as a
suspended substitution is, but what it delays is unfolding a definition, not
substitution: instantiation substitutes into the whole finite template at
once. The type level has no β-redexes, so only the substitution lemma
relating syntactic and semantic substitution carries over.
**Discussed in** [RECURSIVE-EQUATIONS: related work](RECURSIVE-EQUATIONS.md#7-related-work).

### Friedman 1976

E. P. Friedman. *The inclusion problem for simple languages.* Theoretical
Computer Science 1(4):297–316, 1976.
[doi:10.1016/0304-3975(76)90074-8](https://doi.org/10.1016/0304-3975%2876%2990074-8).

**Used for** the undecidability of subtyping: inclusion of simple languages,
those of one-state real-time deterministic pushdown automata accepting by
empty stack, is undecidable. Readonly-record definitions with growing
arguments encode it, since on readonly records inclusion is simulation of
the unfoldings.
**Discussed in** [RECURSIVE-EQUATIONS: subtyping](RECURSIVE-EQUATIONS.md#4-subtyping).

### Kučera and Mayr 2010

Antonín Kučera and Richard Mayr. *On the complexity of checking semantic
equivalences between pushdown processes and finite-state processes.*
Information and Computation 208(7):772–796, 2010.
[doi:10.1016/j.ic.2010.01.003](https://doi.org/10.1016/j.ic.2010.01.003).

**Used for** the conjectured lower bound on deciding subtyping when one side
is regular: simulation between a pushdown process and a finite-state
process, which reduces to that question, is EXPTIME-complete.
**Discussed in** [RECURSIVE-EQUATIONS: subtyping](RECURSIVE-EQUATIONS.md#4-subtyping).

### Pierce 1994

Benjamin C. Pierce. *Bounded quantification is undecidable.* Information and
Computation 112(1):131–165, 1994.
[doi:10.1006/inco.1994.1055](https://doi.org/10.1006/inco.1994.1055).

**Used for** the restriction a subtyping rule between quantified signatures
must take: subtyping in System F<:, whose rule for bounded quantifiers
compares the bounds contravariantly and the bodies under the target's, is
undecidable, so the rule relating two generic methods instantiates the
target's binders rigidly and the source's at them only where the binder
counts are equal and the bounds identical, a decidable check.
**Discussed in** [SOURCE-MODEL: method members are host-relative](SOURCE-MODEL.md#method-members-are-host-relative),
[POSITIVE-TYPES: covered pairs](POSITIVE-TYPES.md#covered-pairs),
`lean/Verification/Types/PositiveRules.lean`.

### Pierce 2002

Benjamin C. Pierce. *Types and Programming Languages.* MIT Press, 2002.

**Used for** the form of the completeness argument for structure-directed
comparison: algorithmic subtyping as syntax-directed rules proved sound and
complete for a declarative system (chapter 16, records with width and depth
subtyping), and subtyping of recursive types as a greatest fixed point decided
by a terminating algorithm (chapter 21). The results concern those calculi;
the selection lemmas here are inversion lemmas of the same kind.
**Discussed in** [UNION-SHAPES: prior work](UNION-SHAPES.md#6-prior-work).

### Castagna and Frisch 2005

Giuseppe Castagna and Alain Frisch. *A gentle introduction to semantic
subtyping.* Invited joint paper of PPDP 2005 and ICALP 2005.
[cduce.org/papers/gentle.pdf](https://www.cduce.org/papers/gentle.pdf).

**Used for** the decomposition of a type by constructor kind before deciding
inclusion as emptiness of a difference, complete for the set-theoretic model
it describes. The outer shapes play the role of the kinds; the completeness
result does not transfer to a model without negation whose record fields are
lifetime contracts of heap locations.
**Discussed in** [UNION-SHAPES: prior work](UNION-SHAPES.md#6-prior-work).

### TypeScript 30779

Ron Buckton. *Relate source types covered by a target discriminated union.*
microsoft/TypeScript pull request #30779, merged 2019-04-29, released in
TypeScript 3.5 ([release notes](https://www.typescriptlang.org/docs/handbook/release-notes/typescript-3-5.html#smarter-union-type-checking)).
[github.com/microsoft/TypeScript/pull/30779](https://github.com/microsoft/TypeScript/pull/30779).

**Used as** the precedent and the contrast for discriminant-directed
comparison: TypeScript decomposes a source object type along its
discriminants' literal types, up to a fixed limit of 25 combinations, and
compares each part with the target union. Selecting target arms by
discriminant carries over; decomposing through a property does not, since
here a property's type constrains every later write.
**Discussed in** [UNION-SHAPES: prior work](UNION-SHAPES.md#6-prior-work).

### Milner et al. 1997

Robin Milner, Mads Tofte, Robert Harper and David MacQueen. *The Definition
of Standard ML (Revised).* MIT Press, 1997.

**Used for** tagged sums: a datatype's constructors are generative, so values
of different constructors are disjoint by construction, and case analysis
selects a branch by constructor. A record discriminant gives a coverage
exclusion from its field types, and disjointness of meanings only at a
successor level under a heap satisfying the world.
**Discussed in** [UNION-SHAPES: prior work](UNION-SHAPES.md#6-prior-work).

### Maranget 2008

Luc Maranget. *Compiling pattern matching to good decision trees.* ACM
SIGPLAN Workshop on ML, 2008.

**Used for** constructor-directed case analysis: matches compiled to decision
trees that test a value's constructor once per node, the cost model indexing
by cell aims at.
**Discussed in** [UNION-SHAPES: prior work](UNION-SHAPES.md#6-prior-work).

### Garrigue 1998

Jacques Garrigue. *Programming with polymorphic variants.* ACM SIGPLAN
Workshop on ML, 1998.

**Used for** tag-directed structural subtyping of variant types: a source tag
is compared with the one target tag of its name, tags disjoint by
construction. The literal-discriminant rule is that rule's selection with the
tag a record field; its lemma proves a coverage exclusion, not disjointness.
**Discussed in** [UNION-SHAPES: prior work](UNION-SHAPES.md#6-prior-work).

## JavaScript and ECMAScript

### ECMA-402

Ecma International, TC39. *ECMAScript Internationalization API Specification*.
[DateTimeFormat constructor and resolved options](https://tc39.es/ecma402/#sec-intl-datetimeformat-constructor).
Scope: formatter construction and the ordinary record returned by `resolvedOptions`.

### ECMA-262

Ecma International, TC39. *ECMAScript Language Specification* (ECMA-262).
The development reads the current draft,
[tc39.es/ecma262](https://tc39.es/ecma262/) (titled *ECMAScript® 2027
Language Specification* as of this writing). Sections relied on by name:

- [Map constructor](https://tc39.es/ecma262/multipage/keyed-collections.html#sec-map-iterable),
  including the return for an undefined input and `AddEntriesFromIterable`,
  for [native collection construction](SOURCE-CONTRACTS.md#library-globals);
- [Array.prototype.splice](https://tc39.es/ecma262/multipage/indexed-collections.html#sec-array.prototype.splice),
  including argument counts, removed holes and inserted values, for the
  [native splice contract](SOURCE-CONTRACTS.md#prototype-contracts);
- [WeakMap objects](https://tc39.es/ecma262/multipage/keyed-collections.html#sec-weakmap-objects),
  including construction and `get`, `set`, `has`, `delete`, for the
  [weak-table native contract](SOURCE-CONTRACTS.md#weak-tables);
- [PromiseResolve](https://tc39.es/ecma262/multipage/control-abstraction-objects.html#sec-promise-resolve),
  [Await](https://tc39.es/ecma262/multipage/control-abstraction-objects.html#await),
  [NewPromiseResolveThenableJob](https://tc39.es/ecma262/multipage/control-abstraction-objects.html#sec-newpromiseresolvethenablejob),
  and the promise resolve functions, which older editions title *Promise
  Resolve Functions* and the 2027 draft defines in
  [CreateResolvingFunctions](https://tc39.es/ecma262/multipage/control-abstraction-objects.html#sec-promise-resolve-functions);
- [Array iterator objects](https://tc39.es/ecma262/multipage/indexed-collections.html#sec-array-iterator-objects)
  (CreateArrayIterator and `%ArrayIteratorPrototype%.next`), for the
  [native footprint](SOURCE-CONTRACTS.md#native-footprints) of `%Iterate%`;
- [Array.prototype.join](https://tc39.es/ecma262/multipage/indexed-collections.html#sec-array.prototype.join)
  and `JoinIndexedProperties`, for the sparse receiver and standard conversion
  in [prototype contracts](SOURCE-CONTRACTS.md#prototype-contracts);
- [ArraySpeciesCreate](https://tc39.es/ecma262/multipage/ordinary-and-exotic-objects-behaviours.html#sec-arrayspeciescreate),
  used by [Array.prototype.map](https://tc39.es/ecma262/multipage/indexed-collections.html#sec-array.prototype.map),
  [filter](https://tc39.es/ecma262/multipage/indexed-collections.html#sec-array.prototype.filter)
  and [slice](https://tc39.es/ecma262/multipage/indexed-collections.html#sec-array.prototype.slice)
  to consult the receiver's constructor and its `Symbol.species`;
- [JSON.parse](https://tc39.es/ecma262/multipage/structured-data.html#sec-json.parse)
  and [InternalizeJSONProperty](https://tc39.es/ecma262/multipage/structured-data.html#sec-internalizejsonproperty);
- [Number::equal](https://tc39.es/ecma262/multipage/ecmascript-data-types-and-values.html#sec-numeric-types-number-equal),
  `IsStrictlyEqual`, [IsLooselyEqual](https://tc39.es/ecma262/multipage/abstract-operations.html#sec-islooselyequal),
  `StringToNumber`, `StringToBigInt`, `ToString`/`Number::toString`, `ToPropertyKey`,
  `ToBoolean`, `typeof`;
- the evaluation of a condition: [binary logical operators](https://tc39.es/ecma262/#sec-binary-logical-operators),
  [logical NOT](https://tc39.es/ecma262/#sec-logical-not-operator),
  the [conditional operator](https://tc39.es/ecma262/#sec-conditional-operator),
  the [comma operator](https://tc39.es/ecma262/#sec-comma-operator) and
  the [`if` statement](https://tc39.es/ecma262/#sec-if-statement) (each
  operand evaluated at most once, left to right, the condition read by
  `ToBoolean`);
- [OrdinaryCallBindThis](https://tc39.es/ecma262/#sec-ordinarycallbindthis),
  [EvaluateCall](https://tc39.es/ecma262/multipage/ecmascript-language-expressions.html#sec-evaluatecall),
  [bound function exotic objects](https://tc39.es/ecma262/multipage/ordinary-and-exotic-objects-behaviours.html#sec-bound-function-exotic-objects-call-thisargument-argumentslist),
  [Function.prototype.apply](https://tc39.es/ecma262/multipage/fundamental-objects.html#sec-function.prototype.apply);
- the object model behind callable values:
  [data types and values](https://tc39.es/ecma262/multipage/ecmascript-data-types-and-values.html)
  (the internal methods `[[Call]]` and `[[Construct]]`, an object with
  `[[Construct]]` also having `[[Call]]`, and property descriptors),
  [functions and classes](https://tc39.es/ecma262/multipage/ecmascript-language-functions-and-classes.html),
  [fundamental objects](https://tc39.es/ecma262/multipage/fundamental-objects.html)
  (`Object.assign` returning its target),
  [control abstraction objects](https://tc39.es/ecma262/multipage/control-abstraction-objects.html)
  (async and generator control state) and
  [ordinary and exotic objects](https://tc39.es/ecma262/multipage/ordinary-and-exotic-objects-behaviours.html)
  (bound functions and proxies);
- iteration: [GetIterator](https://tc39.es/ecma262/#sec-getiterator),
  [ForIn/OfBodyEvaluation](https://tc39.es/ecma262/#sec-runtime-semantics-forin-div-ofbodyevaluation-lhs-stmt-iterator-lhskind-labelset)
  and [IteratorClose](https://tc39.es/ecma262/#sec-iteratorclose) (an early
  exit calls `return` only where the iterator has one),
  [%ArrayIteratorPrototype%.next](https://tc39.es/ecma262/#sec-%arrayiteratorprototype%.next)
  (the length read at each step),
  [%StringIteratorPrototype%.next](https://tc39.es/ecma262/#sec-%stringiteratorprototype%.next)
  (code points), [CreateSetIterator](https://tc39.es/ecma262/#sec-createsetiterator)
  and [CreateMapIterator](https://tc39.es/ecma262/#sec-createmapiterator)
  (a fresh entry array per step), the
  [%IteratorPrototype%](https://tc39.es/ecma262/#sec-%iteratorprototype%-object)
  (its `[Symbol.iterator]` returns the iterator; no `return`),
  [IteratorBindingInitialization](https://tc39.es/ecma262/#sec-runtime-semantics-iteratorbindinginitialization)
  of a rest element and
  [ArgumentListEvaluation](https://tc39.es/ecma262/#sec-runtime-semantics-argumentlistevaluation)
  of a spread;
- [InstanceofOperator](https://tc39.es/ecma262/multipage/ecmascript-language-expressions.html#sec-instanceofoperator)
  (a static `[Symbol.hasInstance]` called, its result converted by
  `ToBoolean`), [Private Names](https://tc39.es/ecma262/multipage/ecmascript-data-types-and-values.html#sec-private-names)
  and [PrivateFieldGet](https://tc39.es/ecma262/multipage/ordinary-and-exotic-objects-behaviours.html#sec-privatefieldget)
  (a private name a key of its own, a missing slot a throw),
  [ClassStaticBlockDefinition](https://tc39.es/ecma262/multipage/ecmascript-language-functions-and-classes.html#sec-class-definitions)
  evaluation, and the `try` statement's completions (a `break` or
  `continue` running each `finally` it leaves);
- arrays and prototypes: [IsArray](https://tc39.es/ecma262/#sec-isarray)
  (`Array.isArray` holds of exactly the Array exotic objects),
  [ArrayCreate](https://tc39.es/ecma262/#sec-arraycreate) (an array's
  prototype is the one its creator passes, `Array.prototype` for the built-ins'
  own constructors), [Object.create](https://tc39.es/ecma262/#sec-object.create),
  [Object.setPrototypeOf](https://tc39.es/ecma262/#sec-object.setprototypeof)
  and [Reflect.construct](https://tc39.es/ecma262/#sec-reflect.construct)
  (any object may be given any prototype, a class's included, without its
  constructor running): the array invariant and why no class invariant is
  assumed.
- the bitwise operators of the compiler API's flag tests:
  [binary bitwise operators](https://tc39.es/ecma262/#sec-binary-bitwise-operators),
  [bitwise NOT](https://tc39.es/ecma262/#sec-bitwise-not-operator),
  the [left shift](https://tc39.es/ecma262/#sec-left-shift-operator),
  [signed right shift](https://tc39.es/ecma262/#sec-signed-right-shift-operator)
  and [unsigned right shift](https://tc39.es/ecma262/#sec-unsigned-right-shift-operator)
  operators, [ToInt32](https://tc39.es/ecma262/#sec-toint32) and
  [ToUint32](https://tc39.es/ecma262/#sec-touint32); the array operations a
  node list meets, and the own-key operations restricted on host values:
  [IsConcatSpreadable](https://tc39.es/ecma262/#sec-isconcatspreadable),
  [FlattenIntoArray](https://tc39.es/ecma262/#sec-flattenintoarray) and
  [EnumerateObjectProperties](https://tc39.es/ecma262/#sec-enumerate-object-properties);
  and [module namespace exotic objects](https://tc39.es/ecma262/#sec-module-namespace-exotic-objects)
  (their members immutable bindings).

**Used for** the meaning of every calculus step and every host row of the
trust surface; checked by review and `#guard` tests against node, not proved.
**Discussed in** [TRUST-REDUCTION: the host](TRUST-REDUCTION.md#the-host),
[SOURCE-MODEL](SOURCE-MODEL.md),
[DESIGN: trust surface](DESIGN.md#trust-surface),
[SEMANTICS: operational language](SEMANTICS.md#operational-language),
[SEMANTICS: graph code](SEMANTICS.md#graph-code),
[SEMANTICS: the array invariant](SEMANTICS.md#the-array-invariant),
[SOURCE-CONTRACTS: async functions and await](SOURCE-CONTRACTS.md#async-functions-and-await),
[SOURCE-ELABORATION: loops and spreads over iterables](SOURCE-ELABORATION.md#loops-and-spreads-over-iterables),
[SOURCE-ELABORATION: patterns](SOURCE-ELABORATION.md#patterns),
[SOURCE-CONTRACTS: classes](SOURCE-CONTRACTS.md#classes),
[CALLABLES](CALLABLES.md), [REQUEST-PROTOCOL](REQUEST-PROTOCOL.md),
[COMPILER-API](COMPILER-API.md),
[the callable examples](../pipeline/examples/callables/README.md).

### JISET and ESMeta

Jihyeok Park, Jihee Park, Seungmin An and Sukyoung Ryu. *JISET: JavaScript
IR-based Semantics Extraction Toolchain.* Proceedings of the 35th IEEE/ACM
International Conference on Automated Software Engineering (ASE 2020),
pp. 647–658, 2020.
[doi:10.1145/3324884.3416632](https://doi.org/10.1145/3324884.3416632).
ESMeta, JISET's successor, is the ECMAScript specification metalanguage and
toolchain at [github.com/es-meta/esmeta](https://github.com/es-meta/esmeta).

**Candidate** for the mechanized ECMA-262 semantics M of a connection: it
extracts the semantics from the specification's own algorithm text and
covers promises and async.
**Discussed in** [TRUST-REDUCTION: the host](TRUST-REDUCTION.md#the-host).

### Bodin et al. 2014 (JSCert)

Martin Bodin, Arthur Charguéraud, Daniele Filaretti, Philippa Gardner, Sergio
Maffeis, Daiva Naudžiūnienė, Alan Schmitt and Gareth Smith. *A trusted
mechanised JavaScript specification.* Proceedings of the 41st ACM
SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL 2014),
pp. 87–100. [doi:10.1145/2535838.2535876](https://doi.org/10.1145/2535838.2535876).

**Context.** A Coq specification of ECMAScript 5 with a certified reference
interpreter; an alternative, hand-written route to M, which predates promises.
**Discussed in** [TRUST-REDUCTION: the host](TRUST-REDUCTION.md#the-host).

## Web platform standards

### HTML

WHATWG. *HTML Living Standard*,
[html.spec.whatwg.org](https://html.spec.whatwg.org/). Sections relied on:
[the 2D rendering context](https://html.spec.whatwg.org/multipage/canvas.html#2dcontext)
(`CanvasTextDrawingStyles`, `measureText`, `TextMetrics`),
[the canvas element](https://html.spec.whatwg.org/multipage/canvas.html#the-canvas-element)
and [`OffscreenCanvas`](https://html.spec.whatwg.org/multipage/canvas.html#the-offscreencanvas-interface)
(`getContext`), `Window`'s
[`document`](https://html.spec.whatwg.org/multipage/nav-history-apis.html#dom-document-2)
and [`navigator`](https://html.spec.whatwg.org/multipage/system-state.html#dom-navigator),
[`NavigatorID`](https://html.spec.whatwg.org/multipage/system-state.html#navigatorid),
`HTMLElement`'s [`lang`](https://html.spec.whatwg.org/multipage/dom.html#dom-lang)
and [forgiving-base64 decode](https://infra.spec.whatwg.org/#forgiving-base64-decode)
for `atob`.
**Relied on in** [the DOM's canvas, document and navigator](SOURCE-CONTRACTS.md#the-doms-canvas-document-and-navigator).

### DOM

WHATWG. *DOM Living Standard*, [dom.spec.whatwg.org](https://dom.spec.whatwg.org/):
[`createElement`](https://dom.spec.whatwg.org/#dom-document-createelement)
and [`documentElement`](https://dom.spec.whatwg.org/#dom-document-documentelement).
**Relied on in** [the DOM's canvas, document and navigator](SOURCE-CONTRACTS.md#the-doms-canvas-document-and-navigator).

### CSSOM

W3C. *CSS Object Model*, [drafts.csswg.org/cssom](https://drafts.csswg.org/cssom/):
[`getComputedStyle`](https://drafts.csswg.org/cssom/#dom-window-getcomputedstyle)
and resolved values.
**Relied on in** [the DOM's canvas, document and navigator](SOURCE-CONTRACTS.md#the-doms-canvas-document-and-navigator).

### Web IDL

WHATWG. *Web IDL Standard*, [webidl.spec.whatwg.org](https://webidl.spec.whatwg.org/):
[attributes](https://webidl.spec.whatwg.org/#es-attributes) as accessor
properties of the interface prototype object, and the conversions to
[DOMString](https://webidl.spec.whatwg.org/#es-DOMString) and
[`[EnforceRange]` integers](https://webidl.spec.whatwg.org/#EnforceRange).
**Relied on in** [the DOM's canvas, document and navigator](SOURCE-CONTRACTS.md#the-doms-canvas-document-and-navigator).

## Promises and flattened types

The nested-promise case: resolution adopts a thenable, so no built-in promise is
fulfilled with one, and a generic signature is truthful at `Promise<T>` only
for a non-thenable `T`. These issues discuss the same fact from the ReScript
and TypeScript sides. It is used in
[TRUST-REDUCTION: illustration](TRUST-REDUCTION.md#illustration-nested-promises),
[SOURCE-CONTRACTS: async functions and await](SOURCE-CONTRACTS.md#async-functions-and-await)
and the promise row of [DESIGN: trust surface](DESIGN.md#trust-surface).

### ReScript 5707

Cristiano Calcagno (cristianoc). *Explore ideas about flattened types.*
rescript-lang/rescript issue #5707, opened 2022-09-29.
[github.com/rescript-lang/rescript/issues/5707](https://github.com/rescript-lang/rescript/issues/5707).

Cited as ReScript #5707 in [TRUST-REDUCTION: illustration](TRUST-REDUCTION.md#illustration-nested-promises).

**Used for** the notion of a flattening constructor,
$`c\langle c\langle t\rangle\rangle = c\langle t\rangle`$ at run time (nullable values,
promises), and the conclusion that a generic signature is truthful at
$`c\langle T\rangle`$ only for $`T`$ outside $`c`$'s image.

### ReScript 5709

Cristiano Calcagno (cristianoc). *Safe promises.* rescript-lang/rescript pull
request #5709, opened 2022-10-01, merged.
[github.com/rescript-lang/rescript/pull/5709](https://github.com/rescript-lang/rescript/pull/5709).

**Context** for making promise types sound against thenable adoption.
**Cited in** [TRUST-REDUCTION: illustration](TRUST-REDUCTION.md#illustration-nested-promises).

### ReScript 6433

dodomorandi. *Should we make async/await work on "thenables"?*
rescript-lang/rescript issue #6433, opened 2023-10-11.
[github.com/rescript-lang/rescript/issues/6433](https://github.com/rescript-lang/rescript/issues/6433).

**Context** for `%Await%` refusing a non-promise object operand: `await`
calls an object's callable `then`
([SOURCE-CONTRACTS: async functions and await](SOURCE-CONTRACTS.md#async-functions-and-await)).
**Cited in** [TRUST-REDUCTION: illustration](TRUST-REDUCTION.md#illustration-nested-promises).

### ReScript 2345

Hongbo Zhang (bobzhang). *sound js promise.* rescript-lang/rescript issue
#2345, opened 2017-12-10.
[github.com/rescript-lang/rescript/issues/2345](https://github.com/rescript-lang/rescript/issues/2345).

**Context**: the early statement that JavaScript promises cannot be typed
soundly at every type parameter. **Cited in** [TRUST-REDUCTION: illustration](TRUST-REDUCTION.md#illustration-nested-promises).

### ReScript 5211

praveen-kumar-rr. *Promise nested inside an option is throwing error.*
rescript-lang/rescript issue #5211, opened 2021-07-09.
[github.com/rescript-lang/rescript/issues/5211](https://github.com/rescript-lang/rescript/issues/5211).

**Context**: a run-time witness of two flattening constructors (option and
promise) composed. **Cited in** [TRUST-REDUCTION: illustration](TRUST-REDUCTION.md#illustration-nested-promises).

### TypeScript 27711

delautour. *Promise<Promise<T>> cannot exist in JS.* microsoft/TypeScript
issue #27711, opened 2018-10-11.
[github.com/microsoft/TypeScript/issues/27711](https://github.com/microsoft/TypeScript/issues/27711).

**Context**: the nested type TypeScript admits and JavaScript never produces. **Cited in** [TRUST-REDUCTION: illustration](TRUST-REDUCTION.md#illustration-nested-promises).

### TypeScript 59111

eps1lon. *Nested Promise not automatically unwrapped.* microsoft/TypeScript
issue #59111, opened 2024-07-02.
[github.com/microsoft/TypeScript/issues/59111](https://github.com/microsoft/TypeScript/issues/59111).

**Context**: a generic instantiation producing the nested type. **Cited in**
[TRUST-REDUCTION: illustration](TRUST-REDUCTION.md#illustration-nested-promises).

### TypeScript 49946

ChrisHamilton91. *Should infer that resolved value of awaited generic Promise
does not extend Promise.* microsoft/TypeScript issue #49946, opened
2022-07-19.
[github.com/microsoft/TypeScript/issues/49946](https://github.com/microsoft/TypeScript/issues/49946).

**Context** for the non-thenable bound on promised type parameters
(`promisedBinders`). **Cited in** [TRUST-REDUCTION: illustration](TRUST-REDUCTION.md#illustration-nested-promises).

### TypeScript 55408

rotu. *Cannot await Thenable.* microsoft/TypeScript issue #55408, opened
2023-08-17.
[github.com/microsoft/TypeScript/issues/55408](https://github.com/microsoft/TypeScript/issues/55408).

**Context** for awaiting a thenable that is not a promise. **Cited in**
[TRUST-REDUCTION: illustration](TRUST-REDUCTION.md#illustration-nested-promises).

### TypeScript 35419

Yogu. *Strict await.* microsoft/TypeScript issue #35419, opened 2019-11-29.
[github.com/microsoft/TypeScript/issues/35419](https://github.com/microsoft/TypeScript/issues/35419).

**Context** for refusing `await` of a non-promise object. **Cited in**
[TRUST-REDUCTION: illustration](TRUST-REDUCTION.md#illustration-nested-promises).

## Compilation

### Aho, Lam, Sethi and Ullman 2006

Alfred V. Aho, Monica S. Lam, Ravi Sethi and Jeffrey D. Ullman.
*Compilers: Principles, Techniques, and Tools*, second edition.
Addison-Wesley, 2006.

**Used for** the short-circuit ("jumping code") translation of a Boolean
condition into branches (section 6.6.3, flow-of-control statements, and
6.6.4, control-flow translation of Boolean expressions): `B.true` and
`B.false` passed down, `!` exchanging them, `&&` and `||` evaluating their
right operand only where the left one does not decide. The translation there
is of a three-address language; the correspondence with JavaScript's
evaluation is argued where it is used.
**Discussed in** [SOURCE-ELABORATION: conditions](SOURCE-ELABORATION.md#conditions).

## Tools

### TypeScript

Microsoft. *TypeScript* ([typescriptlang.org](https://www.typescriptlang.org/)),
its checker and its library declarations (`lib.*.d.ts`), and the handbook's
[More on Functions](https://www.typescriptlang.org/docs/handbook/2/functions.html).

**Used for** name resolution, computed and contextual types, and the library
contracts the overlays filter: a trusted tool of the pipeline. The handbook
states that call signatures, properties and construct signatures coexist in one
object type. Its downlevel emit of a generator as a state machine is the
lowering a generator would take.
**Discussed in** [DESIGN: principles](DESIGN.md#principles),
[DESIGN: trust surface](DESIGN.md#trust-surface), [CALLABLES](CALLABLES.md),
[COMPILER-API](COMPILER-API.md) (its compiler API as a host library).

### typescript-go

Microsoft. *typescript-go*, the Go implementation of TypeScript 7
([github.com/microsoft/typescript-go](https://github.com/microsoft/typescript-go)),
whose build the front end's `typescript` package is; the installed version
7.0.2 names its revision `2bd066d87f5bafd315be9f40889d0a60b9e58e0b` as its
`gitHead`.

**Used for** auditing the server side of the compiler API at that revision:
how the parser constructs a node kind and how the encoder sets the child
presence bits the client's getters read.
**Discussed in** [COMPILER-API: audited shapes](COMPILER-API.md#audited-shapes).

### Node.js modules

OpenJS Foundation. *Node.js documentation: Modules: ECMAScript modules*,
section "Resolution algorithm specification" (`ESM_RESOLVE`,
`PACKAGE_RESOLVE`, `PACKAGE_SELF_RESOLVE`, `LOOKUP_PACKAGE_SCOPE`),
[nodejs.org/api/esm.html](https://nodejs.org/api/esm.html#resolution-algorithm-specification).

**Used for** the files a Node resolution reads: the package scope's and each
ancestor's `package.json`, each ancestor's `node_modules/<package>` up to the
first that exists, and the resolved file. These are the observations a
replayed parse records for a resolution.
**Discussed in** [STAGE-STORE: observed stages](STAGE-STORE.md#observed-stages).

### SKStore

SkipLabs. *SKStore: a generic framework for reactive programming.* The Skip
language's documentation, `skiplang/docs/SKStore.md`, in
[github.com/SkipLabs/skip](https://github.com/SkipLabs/skip).

**Used for** the model of shared work: input directories, derived entries
computed from named inputs, lazy entries computed on demand, and a
computation's dependencies being exactly what it read, so that sharing and
invalidation follow from its read set.
**Discussed in** [shared work](STAGE-STORE.md#shared-work).

### Lean 4

Leonardo de Moura and Sebastian Ullrich. *The Lean 4 theorem prover and
programming language.* CADE-28, LNCS 12699, pp. 625–635, Springer, 2021.
[doi:10.1007/978-3-030-79876-5_37](https://doi.org/10.1007/978-3-030-79876-5_37).

**Used as** the authority: the model, the rules, their soundness proofs and
the checker that consumes producer evidence.
**Discussed in** [DESIGN: what "verified" means](DESIGN.md#what-verified-means).

### wasm-bindgen

The wasm-bindgen contributors. *The wasm-bindgen Guide*: [numeric types](https://wasm-bindgen.github.io/wasm-bindgen/reference/types/numbers.html),
[deployment targets](https://wasm-bindgen.github.io/wasm-bindgen/reference/deployment.html), and
[release 0.2.130](https://github.com/wasm-bindgen/wasm-bindgen/releases/tag/0.2.130).

**Used for** the Rust demo's numeric ABI mapping and its optional
real build: matching crate/CLI versions, generated JavaScript, declarations
and Wasm. The signature agreement check is unproved; the concrete run is
regression evidence, and no cross-language composition theorem is claimed.
**Discussed in** [the Rust demo](../demo/rust/README.md#build-and-execute-the-real-crossing).
