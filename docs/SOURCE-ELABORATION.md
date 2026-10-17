# Search and source forms

Source verification requires evidence for the core judgments and a lowering of
source operations that preserves their meaning. This document specifies that
evidence search and lowering, including patterns, mutable bindings, closures
and parameter initialization.

The prerequisites are the expression, graph and heap judgments in
[Program typing](PROGRAM-TYPING.md), the operational language and worlds in
[Semantics](SEMANTICS.md), and graph types and checked subsumption in
[Positive types](POSITIVE-TYPES.md). Types are finite unions of graph labels;
$`\Gamma`$ assigns types to variables, and $`\Gamma\vdash_G t:A`$ is the core
judgment for a term $`t`$ in graph $`G`$. Supplied point claims fix a graph node's
entry context and expression result type; every incoming edge must justify that
context. Declaration and library contracts used by lowering are specified in
[Reading the source](SOURCE-CONTRACTS.md). The source fragment and refusal
boundaries are specified in [Source fragment](SOURCE-FRAGMENT.md).

## Producing evidence from supplied claims

The producer selects checked effects and propagates their postconditions along
single-predecessor administrative paths within a statement. A source entry is
seeded with exactly its supplied knowledge, without waiting for its predecessors;
every incoming edge must subsequently justify it. External entry starts empty.
There is no iteration to infer a loop invariant. The independent source consumer
enforces the reset, so supplying a graph-safe certificate with extra facts at a
statement entry still fails source verification.

[CertificateProducer.lean](../lean/Verification/Programs/CertificateProducer.lean) accepts an actual graph, its declared result type and
start label, and one `PointClaim` per node. Each claim fixes both the entry
context and the expression result type. These are annotations in this Lean
interface. The source adapter supplies them for the supported
fragment; new source forms require the corresponding extraction obligations.
[DirectProof.lean](../lean/Verification/Programs/DirectProof.lean) holds the recipes for source closures: untrusted plans fixing rule structure and intermediate types.

`produceUsing` builds expression derivation trees and per-slot subtype evidence for
every actual edge. It does not infer or repair point invariants. Its inputs also
include an enumeration of type labels, a search-depth limit, and optional
intermediate type hints. The vocabulary includes singleton labels, their
reference/arrow operands, bottom, and the supplied context/result types. Omitting
labels or useful intermediate types can prevent success, but cannot make an
incorrect certificate pass.

Expression search covers the current ordinary rules: variables, constants,
overloaded lambdas, application, lets, allocation, reads, writes, known shape
answers and subsumption. Subtype search first tries union inclusion, then builds
a finite candidate cyclic relation and removes unsupported rows. It generates
arrow evidence for source selection, splitting union domains, and pairwise
compatible codomain combination. The existing subtype checker validates the
resulting table and all arrow evidence. This search is deliberately incomplete:
it does not enumerate arbitrary intermediate types, transitivity derivations,
or arbitrary nested arrow-combination proofs.

The semantic coverage rule `CallArrow` admits ordered parameter lists.
Source selection checks inclusion contravariantly at every argument position,
with equal actual counts. A union may split at any position while preserving
its prefix and suffix. An empty type at any position makes the domain
uninhabited; an empty parameter list itself still admits a zero-argument call.
Result combination uses the same compatibility check and shared-execution
argument as unary overloads. Graph signatures use domain lists directly,
and `checkArrowWith` checks `CallArrow` derivations (`checkArrowWith_sound`). Search splits unions at any parameter position. Function-creation rules
check that every signature offers at least the descriptor's arity and type the
body under the parameters the code takes, followed by captures. Application evidence and source
lowering still expose unary calls; accepted source programs have not widened.

The final `acceptUsing` check binds the evidence to **all the requested point claims**
as well as calling `checkEntryUsing` on the actual program and external input context. Thus a valid certificate
for different annotations is rejected. `acceptUsing_eq` states its acceptance condition:

```math
\mathrm{acceptUsing}(G,\mathit{images},R,P,Q,C,p,\Gamma_0)=\mathsf{true}
\iff
\mathrm{claims}(C)=Q
\;\land\;
\mathrm{checkEntryUsing}(G,\mathit{images},R,P,C,p,\Gamma_0)=\mathsf{true}.
```

Here $`Q`$ contains the supplied point annotations and $`\Gamma_0`$ is the
independent input contract. Search fuel is not an execution budget and never
occurs in the typing rules or certificates. `accepted_from_inputs` obtains
safety for arbitrary typed arguments from the consumer alone. The producer
can be replaced without changing the soundness argument.

Expression evidence validation uses `ProgramCertificates.checkTreeResult` in a
single traversal. Its coercion and member-coverage checks retain the requested
subtype judgment and resource exhaustion in `CheckResult`, the result shared
with proposal search.
`checkTreeUsing_eq` proves that the acceptance projection has exactly the
declarative rule premises. `ExpressionClaims.checkResult` additionally checks
label validity, the requested root judgment and term scope. Member coverage checks parameter, rest, result
and receiver comparisons through the common subtype operation and checks effects
and arity directly. `checkCallProofs_accepted`, `checkRestProofs_accepted` and
`checkMemberProofs_accepted` prove agreement with the declarative coverage premises.
Signature alternatives retain exhaustion when none succeeds. These results
concern expression evidence; the program acceptance and safety implications
above remain the semantic boundary.

`HeapExpressionRules.checkStepResult` combines expression validation with the
step's heap-fact premises and returns its guaranteed postcondition together with
any unfinished subtype comparison. `checkStepUsing` is its postcondition
projection. `checkStepUsing_eq` proves that the projection has exactly the
step premises and postconditions used by `checkStep_sound`. Effect-candidate
search retains unfinished step validation when no candidate succeeds.

`PointClaims` validates plain and mapped edges through `CheckResult`;
each required slot comparison uses the common subtype operation.
`BranchRefinement.checkObservedResult` additionally checks the observed slot and
admits ordinary, field-slice and structural refinement alternatives. A successful
alternative establishes the edge; otherwise unfinished comparisons are retained.
The modules' `*_eq` theorems prove that their acceptance projections have the
premises consumed by the environment-transport and refinement soundness proofs.

`ControlFlow.checkNodeResult` composes handler, expression-postcondition and
continuation checks. `checkGraphResult` enumerates the program's nodes and
checks source coherence; `checkEntryResult` additionally checks the external
input environment. Their results retain unfinished comparisons from expressions,
heap steps and outgoing edges. Their `*_eq` theorems identify the acceptance
conditions used by graph safety and parameter-reassignment proofs.

`GraphCode` composes definition-effect and graph-entry results. Code admission
extends the checked table in declaration order through `extendTableResult`;
`checkCodesResult` starts from the empty table. An unfinished comparison prevents
admission and retains its resource outcome. `codeCheckedUsing_eq` and
`extendTable_eq` prove the acceptance and table projections used by
`codeChecked_sound` and `checkCodes_sound`.

`RequestJson.verifyResult` returns the code table justified by request validation.
`verifyResult_hasTable` proves that its successful value is exactly the checked
table. `SourceExtraction.checkRequestResult` validates source assertions and
uses that table for supplemental expression obligations. `checkRequestsResult`
requires exact bundle lengths and checks every unit. `checkRequestResult_accepted_iff`
proves the graph, assertion and supplemental premises of a unit, and
`checkRequests_eq` of every requested unit; these premises justify the source safety and supplemental-typing theorems.

An `Exhaustion` carries `CheckFrame` scopes for the node, code entry, supplemental
obligation and source unit enclosing its comparison. `CheckResult.at` and
`allLocated` add these scopes; `accepted_at` and `accepted_allLocated`
prove that they preserve acceptance. Source reporting uses
these scopes to select the corresponding source map or obligation span. A
synthetic node is reported at its enclosing graph's source region.
`SourceExtraction.validationFailure` reports the retained subtype judgment and
resource outcome. Source evidence production and consumption use this reporting
boundary. `RequestJson.validationFailure` selects the graph or code entry named
by a request check's scopes. JSON checking and final response validation report
its retained result at the certificate-check phase. Code admission also reports
unfinished validation before a later expression can depend on that code.
`CertificateProducer.produceUsing` consumes the same retained acceptance result;
its failed-edge diagnostic inspects heap entailment after a completed refusal.

Failure reports a claim-count mismatch, an expression label, an edge's source
and destination, or final consumer rejection. Failure means unsupported or
unjustified within this search, not a proof that the program is untypable.
No evidence is returned as successful unless the consumer accepts it.

The [serialized request protocol](REQUEST-PROTOCOL.md) exposes this path from a
program and its annotations to checked evidence through the verifier binary.
Source extraction correctness, producer completeness and integration of
extended source claims are outside these results.

## Derived source forms

A condition of a Boolean literal type takes only its arm (`ifKnown`): the
pipeline case `known-condition` reaches the rule, and `pipeline/test.mts`
claims its result at that arm alone, a claim refused for
`invalid-known-condition`, whose condition a closure resets. [ExecutionModelTests.lean](../lean/Verification/Tests/ExecutionModelTests.lean) shows the
machine keeping a known condition's write. Source closure blocks support
terminal branches with both arms returning, including nested branches and
checked entry refinements.
Source ternaries reuse these rules and the existing primitive-tag union elimination.
Their own expression claim supplies the result type; both arm claims are checked
under the corresponding refined context. This introduces no additional rule or
trusted proof-search step.
Null coalescing is likewise a derived form: a let saves the left value, and
`unionVar` with known nullish-tag conditionals selects the fallback or saved value.
No truthiness rule is involved; false remains a result of the left operand.

**Shadowing.** JavaScript's scopes nest; the lowering's are lists of
names, each declared once (a second is `duplicate or shadowing local
declaration`). The parser renames instead: a local whose name another
declaration binds in a scope enclosing its own (a module binding, an outer
local or parameter, a named function or class expression's own name) binds
$`x^{@l:c}`$, its spelling and its declaration's line and column
(`x@3:9`, which no source identifier spells), and every identifier
TypeScript binds to that declaration, a shorthand property `{ x }`
included, reads it. This is $`\alpha`$-conversion, which changes no value:

```math
\frac{x\in\mathrm{dom}\Gamma\quad x'=x^{@l:c}\notin\mathrm{names}(\Gamma,S)\quad \Gamma\vdash_R\ \mathsf{const}\ x'=e;\ S[x'/x]}
     {\Gamma\vdash_R\ \mathsf{const}\ x=e;\ S}\ \textsf{shadow}
```

and likewise for `let` (a cell included), parameters, patterns, closure
parameters, `for...of` and `catch` bindings, in function and closure bodies
alike. JavaScript gives the name to the declaration from its block's start,
so a mention of a shadowing local above its declaration, a closure's
included, or in its own initializer is refused by the parser (the temporal
dead zone: JavaScript throws there, and the outer binding is not what it
reads); a pattern element may name one bound before it in the pattern:

```math
\frac{x'\ \text{renames}\ x\ \text{declared at}\ d\quad \text{a mention}\ m\ \text{of}\ x'\quad m<d\ \lor\ m\in\mathit{init}(d)}
     {\text{refused (temporal dead zone)}}
```

**Namespace imports.** A module namespace object's members are the module's
export bindings, read as an import binding reads them
([ECMA-262](REFERENCES.md#ecma-262)). So `import * as ns from M`, where every
mention TypeScript binds to `ns` is a member read `ns.x` or a qualified type
name `ns.T`, is the named import of each member, under a name no other
binding of the file spells:

```math
\frac{\mathrm{mentions}(ns)\subseteq\{\,ns.x_1,\ldots,ns.x_n\,\}\quad ns\$x_i\notin\mathrm{names}(S)}
     {\mathtt{import}\ \ast\ \mathtt{as}\ ns\ \mathtt{from}\ M;\ S\;\equiv\;\mathtt{import}\ \{\,x_1\ \mathtt{as}\ ns\$x_1,\ldots,x_n\ \mathtt{as}\ ns\$x_n\,\}\ \mathtt{from}\ M;\ S[ns\$x_i/ns.x_i]}\ \textsf{namespace-import}
```

A member used only in types is a type import. The parser writes the
elaborated text at the source's offsets (`namespace-imports.mts`): the
namespace import becomes blank text of its length, each `ns.x` the identifier
`ns$x`, and the named imports follow the last statement; a refusal located
in them is reported at the namespace import. A call `ns.f(a)` passes the
namespace object as the receiver, where `ns$f(a)` passes `undefined`; the two
agree for a callee whose signatures state no `this` parameter, and a call of
one that does is refused. Any other mention of `ns` (`const m = ns`,
`ns[k]`, `ns?.x`, `{ ns }`, an export) is refused at the mention.

**A `let` nothing assigns.** A `let` statement whose bindings are all
initialized and which no assignment, compound or logical assignment, update,
destructuring assignment or `for` head in their scope writes (closures
included, found by the name the parser gives each binding) is the `const`
statement: each binding holds its initial value throughout, so a read of it
is that value either way:

```math
\frac{\overline{x}\ \text{initialized}\quad \overline{x}\notin\mathrm{written}(S)\quad \Gamma\vdash_R\ \mathsf{const}\ \overline{x=e};\ S}
     {\Gamma\vdash_R\ \mathsf{let}\ \overline{x=e};\ S}\ \textsf{let-const}
```

So a tag test narrows such a binding as it narrows a `const`, and a `let`
pattern binds. A `let` pattern whose bindings are written binds names no
source spells, as a `const` pattern does, then a `let` of each source name
at its value: a cell of its own, whose contract is an unannotated `let`'s,
its initial value's type widened:

```math
\mathsf{let}\ p = e\;\equiv\;\mathsf{const}\ p[\overline{x\mapsto x^{\circ}}] = e\,;\ \mathsf{let}\ \overline{x = x^{\circ}}
```

JavaScript reads and defaults the pattern's positions, then initializes the
bindings, in that order either way; each cell is claimed at its name, where
its initial value is. Such a pattern in a `for` head is refused. A `let` that is written and holds a union of objects is
not narrowed by a test of its object (a cell's known contents are primitive
values, or that it holds no `undefined`, and a write between the test and the
read may replace it); a read of a member only some arms state is refused
with that reason.

**Shorthand properties.** A shorthand property writes the value its name
reads, as the field of that name, the name resolved as any read of it (a
shadowing local's renaming, above, included):

```math
\{\ldots,\ x,\ \ldots\}\;\equiv\;\{\ldots,\ x\colon x,\ \ldots\}
```

**Older spellings.** `<T>e` is `e as T` and `<const>e` is `e as const`,
the same assertion (an obligation on the operand, never a fact); a
top-level `;`, as one in a body, is nothing.

A derived class's constructor (`class D extends B`, its body
`s̄₁; super(ā); s̄₂`, `s̄₁` reading no `this`) is its base's construction,
bound to a name no source spells, then the class constructor's lowering
([classes](SOURCE-CONTRACTS.md#classes)) whose
allocation is the allocation from parts copying it:

```math
\mathsf{class}(\vec x).\ \vec s_1\,;\ \mathsf{const}\ \textit{base} = \mathsf{new}\ B^{\circ}(\vec a)\,;\
  \mathcal{C}(\vec s_2,\ \varphi_0,\ \varnothing)
  \quad\text{with}\quad
  \mathcal{C}(\varepsilon,\varphi,A) = \{\texttt{[[proto]]}{:}\,D.\texttt{[[prototype]]},\ \ldots\textit{base},\ \varphi,\ \overline{f{:}\,\mathsf{undefined}}\}
```

where $`B^{\circ}`$ is `B`'s constructor claimed also at the fresh instance it
allocates, its keys exact (`ctorGraph` checks its code at that signature too).
`D` without a constructor has JavaScript's implicit one,
`constructor(...args) { super(...args); }`: its parameters are $`B`$'s, at
their types, under names no source spells, and $`\vec a`$ is them. A class's
prototype object is allocated once, at its definition:

```math
D.\texttt{[[prototype]]} = \{\texttt{[[proto]]}{:}\,B.\texttt{[[prototype]]},\ \kappa_D{:}\,\mathsf{undefined},\ m{:}\,D.m,\ \ldots\}
```

its own methods, linked to its base's under the prototype key, as
JavaScript's `D.prototype` is; $`\kappa_D`$, the class's key, is there where
`instanceof D` is written in the file, below. A prototype holding nothing
of its own that nothing tests is not allocated: `D`'s instances then hold
the nearest ancestor's (or none), and every read and test answers the same.
`super.m(ā)` is `B.m.call(this, ā)`, with `B.m` the closure `B`'s prototype
chain holds. So the allocation's keys are exact, and `D`'s declared type,
its own members and `B`'s, covers it through the prototype chain
([method coverage](POSITIVE-TYPES.md#clause-coverage), `CoversByProto`).

A generic method `m<V>(…)` is the instance's member with quantified
signatures ([generic methods](SOURCE-CONTRACTS.md#generic-methods)), and its closure `D.m` a
generic closure, checked once at a scheme received by the instance
(`funScheme`), which the prototype holds. The parser names the closure's
binder $`k`$ by the member's key and the position (`"m"#k`,
the parser's `lambda` in `fragment-expressions.mts`), and the producer's scheme row for the
prototype's field binds those names; the member's scheme binds the
declaration's. The prototype's scheme covers the member bound to the
instance up to renaming the member's binders to its own
([`CoversByScheme`](POSITIVE-TYPES.md#clause-coverage)): its receivers read
none of its binders and hold the instance, and its signatures cover the
member's renamed ones at every instance. A bounded binder is refused, since the row's
name spells its bound.

A method declaring `this: T` is the instance's member whose host must meet
`T` ([records](POSITIVE-TYPES.md#records)), and its closure `D.m` takes `T`
as its receiver, so its body reads `this` at `T`. The prototype's closure
covers the member through the member's `T`, whose values the closure's
receiver admits, whatever the instance type is
([method coverage](POSITIVE-TYPES.md#clause-coverage)); a call on the
instance, `this.m()` among them, proves its host within `T` (`bindMember`).

What a class declaration may not hold, each for its reason:

- a generic method declaring `this: T`: its member is a scheme the member
  bound to its host meets, whatever receiver it is given, which states no
  type the host must meet ([Source model](SOURCE-MODEL.md#method-members-are-host-relative));
- a generic method with a bounded binder: the member's binder row is named by
  its bound, which the closure's binder, named by the parser, is not;
- a constructor parameter default reading `this`, or a constructor statement
  reading it other than as a field assignment's target: the instance is
  allocated at the constructor's end;
- a member with a computed key (a method is a binding and a prototype key
  named by its plain name) other than a static `[Symbol.hasInstance]`,
  below;
- an accessor (reading it runs code; a member read is a plain one), an
  index signature (instances are what construction allocates), a static
  block reading `this` (the class value, which JavaScript's block reaches
  with later static fields undefined and the model allocates only after
  them);
- a private name in inheritance (a derived instance's base part is a copy,
  and a copy holds no private slot), and `#x in o` (it tests an own slot,
  where $`\mathsf{hasKey}`$ walks the prototype chain and would find an
  instance's slot from an object inheriting from it);
- extending a generic class other than at the base's own binders (a generic
  base's construction is at its binders' rows, [classes](SOURCE-CONTRACTS.md#classes)), and
  extending `Array` (its instances are what the library's constructor
  allocates, not an ordinary object).

`e instanceof C`, with `C` an identifier TypeScript binds to a class the
file declares at its top level, evaluates $`e`$, then `C` (read as its
prototype object, which the class statement binds with it), then looks for
$`\kappa_C = \texttt{[[}C\texttt{.prototype]]}`$, the key only
$`C.\texttt{[[prototype]]}`$ owns, along $`e`$'s prototype chain:

```math
e\ \mathtt{instanceof}\ C\;\equiv\;\mathsf{let}\ x=e\ \mathsf{in}\ \mathsf{let}\ p=C.\texttt{[[prototype]]}\ \mathsf{in}\ \mathsf{hasKey}(\kappa_C)(x)
\qquad
\frac{\Gamma\vdash e:A\quad \Gamma\vdash C.\texttt{[[prototype]]}:P}
     {\Gamma\vdash e\ \mathtt{instanceof}\ C:\mathsf{boolean}}
```

Any operand is admitted: $`\mathsf{hasKey}`$ answers `false` on a primitive,
as `instanceof` does (it throws only on its right operand). A tested
immutable variable is refined as by every tag test ([guards](SOURCE-CONTRACTS.md#guards)).

A class whose chain of bases, classes of the file, holds a static method
keyed by the built-in `Symbol.hasInstance` (TypeScript binds the key to the
standard library's `unique symbol` property) answers `instanceof` itself:
ECMA-262's InstanceofOperator calls `C[Symbol.hasInstance]` with the
operand and converts the result by `ToBoolean`, walking no chain. The
method is a static binding $`C.\texttt{[Symbol.hasInstance]}`$ as any static
method is, reading no `this`, so its receiver is unobservable and it is
called plainly; a derived class reads its nearest base's, which its
constructor inherits:

```math
e\ \mathtt{instanceof}\ C\;\equiv\;\mathord{!}\,\mathord{!}\,\big(C.\texttt{[Symbol.hasInstance]}(e)\big)
\qquad
\frac{\Gamma\vdash C.\texttt{[Symbol.hasInstance]}(e):B}
     {\Gamma\vdash e\ \mathtt{instanceof}\ C:\mathsf{boolean}}
```

The operand must meet the method's parameter, as any actual's, and the
test refines nothing: the method's answer says nothing of the operand's
type, where TypeScript narrows it to `C`.

`x instanceof c`, with `c` a name of a value whose type TypeScript gives
states `[Symbol.hasInstance]` (a construct type's readonly
property, met by a class with that static method, which its class value
holds), reads that method off `c` and calls it with `x`, `c` its receiver,
as InstanceofOperator does, and converts the result by `ToBoolean`; `x` is
a name too, so reading `c` first leaves JavaScript's order of the two reads
unobservable:

```math
x\ \mathtt{instanceof}\ c\;\equiv\;\mathord{!}\,\mathord{!}\,\big(c\texttt{[Symbol.hasInstance]}(x)\big)
```

A value whose type does not state the method may still hold one, its
class's: its `instanceof` stays refused.

An optional chain is the same derived form with the arms exchanged. The
parser writes `r?.x` and every link after it in the chain (`.b`, `[k]`,
`(a)`, `!`) as one `optional` node whose body applies those links to the
variable $`\mathsf{chain}`$ (`chainName`, spelled `?.`, which no source
identifier is), so a nullish receiver skips the rest of the chain, as
JavaScript's short-circuit does; a second `?.` in a chain tests the chain so
far, which is `undefined` where an earlier one skipped:

```math
r\,?.\,b\;\equiv\;\mathsf{let}\ \mathsf{chain}=r\ \mathsf{in}\ \mathsf{if}\ \mathsf{nullish}(\mathsf{chain})\ \mathsf{then}\ \mathsf{undefined}\ \mathsf{else}\ b,
\qquad
\frac{\Gamma\vdash r:A\quad T_{\mathsf{false}}(A)::\Gamma\vdash b:B}
     {\Gamma\vdash r\,?.\,b:\{\mathsf{undefined}\mid T_{\mathsf{true}}(A)\neq\emptyset\}\cup B}
```

with $`T_q`$ the nullish tag's slices. The body is checked where the saved
receiver holds its present slice, so a method called through the chain
(`o?.m()`) has the present `o` as its receiver. `o.m?.()` would test the
method but call it with `o`, which the chain does not save apart from the
tested value, and is refused. On a `null` or `undefined` literal receiver the
chain is `r, undefined`: the literal is the receiver's whole value, and the
body never runs.

`typeof e` as a value is the string naming the shape of $`e`$'s value, one tag
test per answer in turn, the operand evaluated once (`typeofTerm`); a value no
test holds of has call code, which `typeof` names `"function"`:

```math
\mathsf{typeof}\ e\;\equiv\;\mathsf{let}\ x=e\ \mathsf{in}\
\mathsf{if}\ \mathsf{isUndef}(x)\ \mathsf{then}\ \texttt{"undefined"}\ \mathsf{else}\
\mathsf{if}\ \mathsf{typeofObject}(x)\ \mathsf{then}\ \texttt{"object"}\ \mathsf{else}\ \cdots\
\mathsf{if}\ \mathsf{isSymbol}(x)\ \mathsf{then}\ \texttt{"symbol"}\ \mathsf{else}\ \texttt{"function"}
```

in the order undefined, object, boolean, number, string, bigint, symbol. It
splits $`x`$ by `unionVar` as `??` does (`selectPlan`), so a label whose shape
is settled reaches one answer; its claim is `string`. A comparison of `typeof e`
with a shape's literal stays the one tag test ([guards](SOURCE-CONTRACTS.md#guards)).

`key in o` evaluates the key, then the object, then asks whether the object
has the key. A string literal key is the tag test $`\mathsf{hasKey}(\kappa)`$ of
the object, which refines a tested immutable variable as every tag test does.
A key whose claim is a union of string singletons $`\kappa_1\mid\cdots\mid\kappa_n`$
dispatches on them, the last needing no test since the key is one of them
(`inKeysTerm`):

```math
k\ \mathtt{in}\ o\;\equiv\;\mathsf{let}\ y=k\ \mathsf{in}\ \mathsf{let}\ x=o\ \mathsf{in}\mathsf{if}\ \mathsf{strEq}(\kappa_1)(y)\ \mathsf{then}\ \mathsf{hasKey}(\kappa_1)(x)\ \mathsf{else}\ \cdots\mathsf{hasKey}(\kappa_n)(x)
```

```math
\frac{\Gamma\vdash o:A\quad \forall\gamma\in\mathrm{expand}_G(A).\ \gamma\ \text{a record, dictionary, arrow or callable clause}
      \quad \kappa_i\notin\mathcal B}
     {\Gamma\vdash k\ \mathtt{in}\ o:\mathsf{boolean}}
```

where $`\mathcal B`$ is the keys the model does not answer as JavaScript does
(`inKeyRefusal`, [guards](SOURCE-CONTRACTS.md#guards)). The operand's clauses are
objects because `in` throws on a primitive, where the test would answer
`false`, and not a class value, which holds its static fields but not the
keys JavaScript's class owns besides (`name`, `length`, `prototype`, its static
methods).

A key TypeScript types as other than string literals (a `string`, a number,
an array index among them, a symbol) may name what the model does not answer
as JavaScript does: a prototype's key, or an array's element, which the store
holds rather than a key. Such a test is the host's, a call of the intrinsic
$`\%\mathsf{HasProperty}\%`$ (`intrinsics.mts`), which the parser writes where
TypeScript's type of the key has another part, and which narrows nothing:

```math
k\ \mathtt{in}\ o\;\equiv\;\%\mathsf{HasProperty}\%(k,\ o)
\qquad
\%\mathsf{HasProperty}\%:(\mathtt{string}\mid\mathtt{number}\mid\mathtt{symbol},\ \mathtt{object})\Rightarrow\mathtt{boolean}
```

The call evaluates the key, then the object, then the lookup, as `in` does;
converting the key runs no code, and neither does the lookup on the objects
a program holds (no proxy, [trust surface](DESIGN.md#trust-surface)).

A read `o[k]` of an object whose key is claimed at a union of string and number
singletons $`\kappa_1\mid\cdots\mid\kappa_n`$ dispatches the same way, each
singleton selecting the read of the key it converts to (a number's, the key
its `ToString` spells), as a literal key's read is (`keySingletons`,
`keyedReadTerm`):

```math
o[k]\;\equiv\;\mathsf{let}\ x=o\ \mathsf{in}\ \mathsf{let}\ y=k\ \mathsf{in}\
\mathsf{if}\ \mathsf{eq}(\kappa_1)(y)\ \mathsf{then}\ \mathsf{readAt}\;\kappa_1\;x\ \mathsf{else}\ \cdots\
\mathsf{readAt}\;\kappa_n\;x
```

with $`\mathsf{eq}`$ the tag `strEq` or `numEq`. It is typed by `unionVar`,
`ifTag` and the read rules alone. NaN is no singleton here, since no equality
test finds it.

Logical AND and OR return an operand, as in JavaScript: the left one where its
truthiness decides, the right one elsewhere. For a left operand that is not a
Boolean they are the same derived form on the truthiness test:

```math
a\mathbin{\&\&}b\;\equiv\;\mathsf{let}\ x=a\ \mathsf{in}\ \mathsf{if}\ \mathsf{truthy}(x)\ \mathsf{then}\ b\ \mathsf{else}\ x,
\qquad
a\mathbin{\Vert}b\;\equiv\;\mathsf{let}\ x=a\ \mathsf{in}\ \mathsf{if}\ \mathsf{truthy}(x)\ \mathsf{then}\ x\ \mathsf{else}\ b,
```

split by `unionVar` on $`x`$ (`selectPlan`, which `??` and default parameters
share): a label whose truthiness is settled selects its arm by `ifTag`, and
one that is not (a number, a string) takes both arms by `ifBool` on the test.
Writing $`T_q(A)`$ for the labels of $`A`$ that may answer $`q`$ (`tagSlice`):

```math
\frac{\Gamma\vdash a:A\quad T_{\mathsf{true}}(A)::\Gamma\vdash b:B}
     {\Gamma\vdash a\mathbin{\&\&}b:T_{\mathsf{false}}(A)\cup B}
\qquad
\frac{\Gamma\vdash a:A\quad T_{\mathsf{false}}(A)::\Gamma\vdash b:B}
     {\Gamma\vdash a\mathbin{\Vert}b:T_{\mathsf{true}}(A)\cup B}
```

The right operand is checked where the saved left operand holds the slice
that reaches it; a named immutable left operand moves to that slot, as for
`??`, so `o && o.a` reads a field of the truthy `o`. The falsy slice is
exactly what `ToBoolean` leaves: of `number`, all of `number`, since `0`, `-0`
and NaN are falsy (TypeScript's `0` there omits NaN). `!a` of a value that is
not a Boolean is $`\mathsf{if}\ \mathsf{truthy}(a)\ \mathsf{then}\ \mathsf{false}\ \mathsf{else}\ \mathsf{true}`$,
by the same split. A condition that is not a Boolean is its truthiness: a
statement guard dispatches with `tagBind` on $`\mathsf{truthy}`$, refining a
tested immutable variable to $`T_q`$ of its type on each edge, and a closure
branch uses the split above. A disjunctive outcome (a false `&&`, a true
`||`) joins at its target, whose entry claim each incoming edge establishes
under its own refinement.

For Boolean left operands, logical AND and OR use the derived forms:

```math
a\mathbin{\&\&}b\;\equiv\;\mathsf{if}\ a\ \mathsf{then}\ b\ \mathsf{else}\ \mathsf{false},
\qquad
a\mathbin{\Vert}b\;\equiv\;\mathsf{if}\ a\ \mathsf{then}\ \mathsf{true}\ \mathsf{else}\ b.
```

They share the source conditional proof builder, including null refinement within
the right operand;
the synthetic constant arm requires a literal proof, not a source claim.
At statement guards the source compiler instead emits short-circuit graph paths,
whose Boolean/null observations justify the intermediate and successor contexts.
It also checks the complete expression claim using the derived expression form.
Thus graph decomposition cannot silently discard the producer's condition type.

A condition read for its truthiness alone, a statement guard's or a
conditional expression's test, is a short-circuit dispatch whatever its left
operand's type. Where that operand is no test (a comparison, a shape or
singleton test, `!`, `in`), the operator's value may be it, not a Boolean;
read for its truthiness, the value is that truthiness:

```math
\mathsf{truth}(a\mathbin{\&\&}b)=\mathsf{truthy}(a)\land\mathsf{truth}(b),
\qquad
\mathsf{truth}(a\mathbin{\Vert}b)=\mathsf{truthy}(a)\lor\mathsf{truth}(b).
```

Each arm of the left operand's dispatch rebinds its outcome, `true` or
`false`, and the right operand runs where the left is truthy (`&&`) or falsy
(`||`), in the context the left operand's outcome leaves: a tested variable
is a Boolean outcome where it is a Boolean, and otherwise the labels of its
type its truthiness admits (`conditionContext`). So `s && r !== "a" ? r : x`
sees `r` at `"b"` in its first arm (`logical-truth-narrowing`), and
`s || r !== "a" ? r : x` does not (`invalid-logical-truth-or-narrowing`).
The dispatch's value is that truth, which no program reads but the test:
it carries no obligation about the operator's value, whose claim is checked
where the operator is read as a value, and each operand keeps its own
(`logical-string-values`: `s && s` of a string in a condition).

A chain of one operator is read right-nested, the parser's left nesting
reassociated:

```math
(a\mathbin{\&\&}b)\mathbin{\&\&}c\;\equiv\;a\mathbin{\&\&}(b\mathbin{\&\&}c),
\qquad
(a\mathbin{\Vert}b)\mathbin{\Vert}c\;\equiv\;a\mathbin{\Vert}(b\mathbin{\Vert}c),
```

which JavaScript evaluates in the same order to the same value (a falsy
$`a`$ is the result either way, and so on). Read so, $`c`$ is checked where $`a`$
and $`b`$ each answered, and the inner operator is typed at the whole's
claim, which covers every value it yields. A variable tested by both $`a`$
and $`b`$ is split twice; the inner split takes, of its planned arms, those
of the labels the outer one left.

Closure branches whose two arms fall through require no additional typing rule.
Their extracted shape is:

```math
\mathsf{let}\ z = (\mathsf{if}\ c\ \mathsf{then}\ t\ \mathsf{else}\ e)
\ \mathsf{in}\ k.
```

Both $`t`$ and $`e`$ finish with an administrative null after their effects.
The existing conditional rules check them at $`\mathsf{Null}`$, and the let rule
checks $`k`$ under $`\mathsf{Null}::\Gamma`$. The new slot is anonymous; source names
refer to their original outer bindings. The source statement at $`k`$ supplies
an environment whose types must be justified from this context. Arm-local
bindings and singleton refinements cannot become assumptions at the join.
The continuation occurs once, so nested branching does not duplicate its term.
`shared_continuation_trace` ties the extracted graph to a 44-step execution in
which the selected arm writes true before the shared read returns true.

An early-return branch with one fully returning arm and one return-free arm
uses the same conditional rules. For example, `if (c) { return r; } else { s; } k`
has the extracted shape

```math
\mathsf{if}\ c\ \mathsf{then}\ r\ \mathsf{else}\quad
(\mathsf{let}\ z=s\ \mathsf{in}\ k).
```

Here $`s`$ completes with administrative null, and its local bindings stay inside
$`s`$. Both $`r`$ and the surviving sequence check at the supplied function result
type. When $`c`$ tests an immutable Boolean variable, the surviving sequence uses
the justified false refinement; it does not have to discard this fact as a
shared join would. `early_return_trace` checks both outcomes of an extracted
closure: an early return skips the later write, while the other arm executes it.
General partially returning nested arms remain gated.

A block closure that does not return on every terminal arm completes, which in
JavaScript returns `undefined`; its body ends with $`\mathsf{return}\ \mathsf{undefined}`$ at the closing brace, so that the shapes above apply
unchanged, and the result claim must admit $`\mathsf{Undef}`$ (`void` is top). A
bare `return` is the same literal at its keyword.

A keyed access `a[k]` whose key is claimed at one string $`s`$ is the named
access of $`\mathsf{str}(s)`$, evaluated after `a` and `k`, and the
[core read rules](PROGRAM-TYPING.md#judgments-and-constructor-views) apply. A key claimed at one number $`n`$ names the property
$`\mathsf{ToString}(n)`$ (`numberToString`), as JavaScript's `ToPropertyKey`
converts it, where `a` is claimed only at records owning no array store
(`recordReceiver`); an array's number key is its store's element (`elemAt`):

```math
\frac{\Gamma\vdash_G a:R\quad R\equiv_G c_1\cup\cdots\cup c_m\ \text{records without a store}\quad
      \Gamma\vdash_G k:\mathsf{Num}(n)}
     {a[k]\ \leadsto\ \mathsf{let}\ x=a\ \mathsf{in}\ \mathsf{let}\ \_=k\ \mathsf{in}\ x.\mathsf{str}(\mathsf{ToString}(n))}
```

([index signatures](SOURCE-CONTRACTS.md#index-signatures)).

A statement `if` whose arm is one `return` of the read its singleton test
tests returns that read's saved value, in a function body and in a closure's
alike (`guardedReturn`). With $`c`$ a literal, a name or a field read, nothing
runs between the two reads of $`x.f`$, so they read the same value:

```math
\mathsf{if}\;(x.f \bowtie c)\;\mathsf{return}\;x.f
\;\leadsto\;
\mathsf{let}\ s=x.f\ \mathsf{in}\ \mathsf{if}\;(s \bowtie c)\;\mathsf{return}\;s
```

and the test's tag edge refines $`s`$ to the slice of its type the arm admits,
which must lie within the returned read's claim. A call or a write in the arm
leaves the shape, and the arm reads anew.

## Patterns

A pattern binds names from one value, in pattern order, and has no rule of its
own: it is reads, a tag dispatch and lets. Write
$`\Gamma\vdash p\Leftarrow(t{:}R)\dashv\Delta`$ when binding pattern $`p`$ to the
value term $`t`$ reads at $`R`$ under $`\Gamma`$ extends the scope by $`\Delta`$
(`bindTarget` in the graph lowering, `closureBind` in a closure body). A name
binds the read; a nested pattern holds it in an anonymous slot and binds its
own elements over it:

```math
\frac{\Gamma\vdash t:R}{\Gamma\vdash x\Leftarrow(t{:}R)\dashv x{:}R}
\qquad
\frac{\Gamma\vdash t:A\quad
      \Gamma,\_{:}A,\Delta_{<i}\vdash p_i\Leftarrow(\mathsf{read}_{f_i}(\_){:}R_i)\dashv\Delta_i\ \ (i\le n)}
     {\Gamma\vdash\{f_1{:}p_1,\ldots,f_n{:}p_n\}\Leftarrow(t{:}A)\dashv\Delta_1,\ldots,\Delta_n}
```

where $`R_i`$ is the type the ordinary read rules give $`f_i`$ of $`A`$ (`readCell`:
an invariant field at its contract, a view at its bound, an optional field at
its type or $`\mathsf{Undef}`$, an inherited member at the prototype's, a union
alternative by alternative); a method is refused, since read off its object
it is no function value. An array pattern is the same with
$`\mathsf{elem}(\mathsf{read}_{[\,]}(\_),i)`$ at the type of position $`i`$
(`positionRead`: a required position at its type, an optional or rest one at
its type or $`\mathsf{Undef}`$), a hole being a position no element names. The
array's own iterator, which JavaScript steps, reads the current length and the
next index at each step (the trust `%Iterate%` states,
[trust surface](DESIGN.md#trust-surface)), and once a step found the end it
stays finished. Reading position $`i`$ where its element is bound, after any
default before it ran, is that step whenever nothing grew the array after a
step found its end: without code between the steps the length is the same at
each, so a later position is past it too. The fragment requires this of a
pattern over an array another reference may hold: no code that may change an
array runs after one of its steps and before a later one
([model limits](SOURCE-FRAGMENT.md#model-limits)). A pattern over a host iterable that
is not an array is refused; one over an iterable the program defines is the
iterator protocol's steps ([loops](SOURCE-CONTRACTS.md#loops-and-spreads-over-iterables)).

A pattern binding a `for...of` binds each element, then reads it, before the
body, as JavaScript binds it per iteration:

```math
\mathtt{for}\ (\mathtt{const}\ p\ \mathtt{of}\ e)\ s\ \rightsquigarrow\ \mathtt{for}\ (\mathtt{const}\ \%e\ \mathtt{of}\ e)\ \{\ \mathtt{const}\ p = \%e;\ s\ \}
```

with $`\%e`$ a name no source spells and the inner declaration a `const`
pattern's; a loop over an iterable the program defines takes no pattern
(`for-of-pattern-binding`, `invalid-for-of-pattern-string`).

A default replaces a read that is `undefined`, and only then runs. With
$`R'`$ the read's labels told apart clause by clause (`byClause`: a label that
is a union row, such as a declared alias, is replaced by one label per
clause, the same values) and $`T_q`$ the tag slice:

```math
\frac{\Gamma\vdash t:R'\quad \Gamma,\_{:}R'\vdash d:D\quad
      \Gamma,\_{:}R'\vdash p\Leftarrow(\mathsf{if}\ \mathsf{isUndef}(\_)\ \mathsf{then}\ d\ \mathsf{else}\ \_\ {:}\ T_{\mathsf{false}}(R')\cup D)\dashv\Delta}
     {\Gamma\vdash (p=d)\Leftarrow(t{:}R)\dashv\Delta}
```

(`tagBind` in a graph, `selectPlan` in a closure). The default is checked
where the earlier bindings are in scope and the later ones are not; a default
that names a later binding of its own declaration is refused by the parser,
since JavaScript throws there (the temporal dead zone) where the lowering
would read an outer binding of that name.

For graph binding plans, a read whose type proves that `isUndef` is false
binds its saved value directly:

```math
\frac{\Gamma\vdash t:R'\quad \mathrm{Answers}(R',\mathsf{isUndef},\mathsf{false})\quad
      \Gamma\vdash p\Leftarrow(t{:}R')\dashv\Delta}
     {\Gamma\vdash(p=d)\Leftarrow(t{:}R)\dashv\Delta}
```

The predicate's semantic guarantee is proved by `ProgramTyping.answers_sound`
in [TypingBasics.lean](../lean/Verification/Programs/TypingBasics.lean).
This specializes the existing conditional semantics. The read occurs once,
and its preceding effects are retained; the default contributes neither
execution nor a type claim. The condition uses the read type derived by the
verifier from its current context. Missing producer claims alone never justify
skipping a default. If the condition is unproved, the default's claims and
execution remain required.

An array rest $`\ldots p`$ at index $`s`$ over $`A`$ whose store is one tuple of
$`n`$ required positions, whose length is exact (`listT`), is the fresh array of
the positions from $`s`$ on, claimed at the rest's span $`C`$ like an array
literal:

```math
\frac{\mathrm{Store}(A)=[A_0,\ldots,A_{n-1}]\quad
      \Gamma\vdash\mathsf{alloc}\{[\,]{:}\mathsf{arr}(\mathsf{elem}(\_,s),\ldots,\mathsf{elem}(\_,n{-}1))\}:C\quad
      \Gamma\vdash p\Leftarrow(\cdot{:}C)\dashv\Delta}
     {\Gamma\vdash[\ldots,\ldots p]\Leftarrow(\_{:}A)\dashv\ldots,\Delta}
```

A rest TypeScript types as no one tuple of required positions (an array, a
union of tuples, a tuple with optional or rest positions) is a **slice**,
marked so by the parser, whose length only the run knows. It is a call of the
trusted intrinsic

```math
\mathtt{\%RestFrom{:}k\%}:\forall T.\ (\mathsf{readonly}\ [\underbrace{\mathsf{unknown}?,\ldots,\mathsf{unknown}?}_{k},\ \ldots T[\,]])\Rightarrow T[\,]
```

on the source, $`k`$ the rest's index, made after the pattern's reads and
defaults: the fresh array of the source's elements from $`k`$ to its current
length, claimed at the rest's span with the call's instance:

```math
\frac{\Gamma\vdash\_:A\quad A\le\mathsf{readonly}\ [\mathsf{unknown}?^k,\ldots T\sigma[\,]]\quad
      \Gamma\vdash p\Leftarrow(\mathtt{\%RestFrom{:}k\%}(\_){:}T\sigma[\,])\dashv\Delta}
     {\Gamma\vdash[\ldots,\ldots p]\Leftarrow(\_{:}A)\dashv\ldots,\Delta}\ \textsf{rest-slice}
```

The parameter says nothing of the first $`k`$ positions, so a union of tuples
of different lengths meets it arm by arm: `[number] | [number, string]` from
1 at $`T=\mathsf{string}`$. JavaScript steps the array's iterator on past the
pattern's elements to the end, reading the length at each step; no code runs
between the call and that stepping, so the call's reading of the current
length is the step's (the trust `%Iterate%` states). A slice in a closure's
directly checked body is refused. An object rest `{ a, ...r }` is the
[allocation from parts](PROGRAM-TYPING.md#allocation-from-parts) copying the source's own
enumerable keys less the ones the pattern names, onto a fresh object.

A statement `const p = e` holds $`e`$ in an anonymous slot for its one entry,
binds $`p`$ over it, and drops the slot before the next entry, which states
$`\Delta`$. An array assignment `[t_1, …, ...t_r] = e` holds $`e`$ likewise;
each target $`t_i`$, in turn, is a mutable local or a field, `o.f` or `o[k]`,
whose reference is evaluated first, the receiver and then the key, into
slots; then its position is read and defaulted, and the value written to the
reference, a local at its storage contract and a field at the field's
writable contract, as an assignment to it writes ([ECMA-262](REFERENCES.md#ecma-262)'s
`IteratorDestructuringAssignmentEvaluation`):

```math
⟦[t_1=d_1,\ldots]=e⟧\;=\;\mathsf{let}\ a=⟦e⟧\ \mathsf{in}\ \mathsf{let}\ \vec s_1=\mathrm{ref}(t_1)\ \mathsf{in}\ \mathsf{let}\ v_1=(a[i_1]\ \mathsf{if\ defined\ else}\ ⟦d_1⟧)\ \mathsf{in}\ \mathrm{put}(\vec s_1,v_1);\ \ldots;\ a
```

where $`\mathrm{ref}(x)`$ is empty, $`\mathrm{ref}(o.f)`$ is $`⟦o⟧`$ and
$`\mathrm{ref}(o[k])`$ is $`⟦o⟧,⟦k⟧`$, and $`\mathrm{put}`$ writes the local, or
the field at the saved receiver and key. A rest's target is evaluated after
the elements before it, and before its fresh array is collected. The read
$`a[i_1]`$ is the iterator's step as in a binding pattern: over an array
another reference may hold, a target's reference evaluated after the first
step, a default, and a write at a field target's index or `length` that run
before a later step change no array. A parameter
written as a pattern or with a default binds a hidden name $`h`$, which the
caller's argument initializes, and the body starts with the pattern over it,
in parameter order:

```math
\mathsf{function}\ f(\ldots,p_i=d_i,\ldots)\,\{S\}\;\equiv\;
\mathsf{function}\ f(\ldots,h_i,\ldots)\,\{\ldots;\ \mathsf{const}\ p_i=h_i\ (\mathsf{default}\ d_i);\ \ldots;\ S\}
```

where $`h_i`$'s type admits $`\mathsf{Undef}`$ when there is a default, so a
caller may omit it. A closure parameter's default stays the closure's own
(`parameterOrder`), and its pattern is a `destructure` first in the body.

## Mutable bindings and module constants

A `let` binding and an assigned parameter lower to a slot of their
activation or to a private cell
([Source model](SOURCE-MODEL.md#mutable-bindings)). Its
contract $`C`$ is fixed where it is declared; the initializer and every write
are checked against it (`storage-contract`). A point claim for the name is
the slot's type there, checked on every incoming edge as any slot's is, or
describes the cell's current contents, which the
[current-content rules](PROGRAM-TYPING.md#current-content-rules-semantic-layer) justify on every
incoming edge.

**Slot or cell.** A cell is how a binding is shared with the closures that
capture it. Write $`\mathrm{writes}(x)`$ for the writes of $`x`$ in its
activation (its declaration's initialization, assignments, updates and
pattern targets), $`\mathrm{creates}(x)`$ for the creations of closures whose
bodies mention $`x`$, each an event of a run of the activation, and $`\prec`$
for the order of the activation's evaluation. Then

```math
\mathrm{slot}(x)\iff
\neg\,\mathrm{closureWrites}(x)\;\land\;
\bigl(\forall c\in\mathrm{creates}(x),\ w\in\mathrm{writes}(x).\ w\prec c\bigr)
\;\land\;\neg\,\mathrm{nestedWrite}(x)
```

where $`\mathrm{nestedWrite}(x)`$ holds when a write of $`x`$ is not its
statement's own: a statement's own write is a declaration's initialization,
or the assignment or update an expression statement is. Under the first two conjuncts every
closure that mentions $`x`$ finds, whenever it runs, the value $`x`$ held when
the closure was created, since no write follows that creation: the closure
may capture that value, and the activation alone reads and writes the
binding. Such a binding is a variable of the activation's environment. Its
slot is rebound at each write, the edge out of the write's node mapping the
written value into it, and a read of $`x`$ is the slot:

```math
\rho \vdash x \mathrel{=} e\ \leadsto\ v\leftarrow e;\ \mathrm{check}_C(v);\ \rho[x\mapsto v]
\qquad
\rho \vdash x\ \leadsto\ \rho(x).
```

The third conjunct is a limit of the lowering, which types the rest of a
statement, and joins the arms of an expression, at the frame the statement
entered with: such a binding stays a cell.
`cellLocals` decides the conjuncts by one walk in evaluation order: the parts
of an expression left to right, statements in order, every part of a choice
(a superset of either arm), and a loop's parts twice, so that a write in one
iteration follows a closure the iteration before created. The decision is
syntactic and selects a lowering; the graph checker checks what either
lowering states. The flow graph exported to the producer lists each body's
cells (`cells`), so the producer and the lowering read one decision.

A slot is part of the environment, which no heap step reaches: its type and
value facts survive a call, a closure run and a throw. A `catch` is entered
from each node that may throw (a node whose expression is a value or a slot
names no handler), with what the slot holds at that node. A cell's contract
is what a closure reads it at; a slot's contract only checks its writes.
After its initialization or a write of a value of type $`V`$, the producer
claims a slot at $`V`$ where $`V`$ is primitive, and otherwise at the arms of
$`C`$ that $`V`$ may be of, those a written literal rules out dropped and a
nullish arm dropped where $`V`$ excludes it (TypeScript's narrowing on
assignment): a read then sees $`C`$'s members, an optional field included,
on every path, and Lean checks $`V`$ below that claim on the edge out of the
write. The contract is:

```math
\mathrm{contract}(\mathtt{let}\ x{:}T=e)=T
\qquad
\mathrm{contract}(\mathtt{let}\ x=e)=
\begin{cases}
Q_{\mathit{next}}(x) & \text{the claim for } x \text{ at the entry of the next statement}\\
Q(e) & \text{no statement follows in its block}
\end{cases}
```

with $`Q(e)`$ the claimed type of the initializer. A declaration ending its block
has no statement after it to read the binding, and the initializer meets its
own claim, so any choice every write is checked against is sound. The producer
proposes TypeScript's declared type, the initializer's type widened
(`let x = 1` stores $`\mathsf{Num}`$). A `null` or `undefined` initializer
has no declared type in TypeScript (an evolving `any`): the producer proposes
the union of what is written into the binding, its evolved type,

```math
\mathrm{contract}(\mathtt{let}\ x=e_0)=\bigcup_{x=e_i}\mathrm{widen}(Q(e_i))
\qquad e_0\in\{\mathtt{null},\mathtt{undefined}\},
```

over the initializer and every assignment of $`x`$ in its scope, closures
included, each read at the contract where it reads $`x`$. Where no fixed
union exists (a value consed onto $`x`$ grows with it), the producer proposes
a contract from the statements after the declaration. In each it examines
the first mention of $`x`$ only, and keeps it where it is a use of the whole
value at a type: a returned value at the result type, an annotated
initializer at its annotation, an argument of a function of one signature
at its parameter: a plain one's, or a generic one's at the instance the
call's own expected type fixes with the actuals unconstrained, where
relating the callee's result to the expected type gives every binder a
bound, so that no binder takes a default and the instance is independent of
$`x`$.
Mentions at no such type are dropped. Where the
kept uses expect one type $`U`$,

```math
\mathrm{contract}(\mathtt{let}\ x=e_0)=U
\qquad \{U\}=\{T\mid \text{a kept use of } x \text{ is expected at } T\},
```

and the proposal is refused where they expect none or several. The
contract is a proposal, not a summary of every use: Lean checks the
initializer and every write against it.
An unannotated `[]` is claimed at the array of what its `push`, `unshift` and
index writes add. Any choice is sound here, since every write is checked
against the contract. A parameter $`x{:}D`$ that the body assigns (`assignsStmt`) has
contract $`D`$, the caller's value its initial contents.

A `let` without an initializer binds `undefined` where its declaration runs,
which is the derived form

```math
\mathtt{let}\ x{:}T;\quad\equiv\quad\mathtt{let}\ x{:}T\cup\mathsf{Undefined}=\mathtt{undefined}.
```

Definite assignment is not an extra rule: a read at $`T`$ types only where the
cell's current contents are known to be in $`T`$, a fact a write of a $`T`$ value
establishes and a join keeps only when every incoming edge proves it. A
closure reads a captured cell at its contract, $`T\cup\mathsf{Undefined}`$,
since it may run before the write; a binding held in a slot is captured at
its value, which every write precedes. Current contents are primitive predicates
or `defined`, which a write of a value whose type rules `undefined` out
records: so a `let x: T;` of an object type `T` assigned on every path is read
at $`T`$ ([`read-sliced`](PROGRAM-TYPING.md#checked-expression-postconditions)), and a call in
between forgets it. Without an annotation there is no contract and the parser
refuses it.

A module constant $`c`$ bound to $`e_c`$ by the initialization unit is read by
the module's functions at

```math
\mathrm{type}(\mathtt{const}\ c{:}T=e_c)=T
\qquad
\mathrm{type}(\mathtt{const}\ c=e_c)=Q_{\mathit{init}}(e_c),
```

the initialization unit's claim for its initializer. That unit checks
$`\Gamma\vdash e_c:Q_{\mathit{init}}(e_c)`$ where it binds $`c`$, exactly as it
checks an annotation, and a constant never changes, so the functions'
assumption is what the unit establishes (the composition argument is
[DESIGN.md](DESIGN.md#modules-and-code-units)'s, unchanged).

A non-generic class $`C`$ bound by the initialization unit at its type
$`K_C`$ is read by its own methods, static ones included, and constructor, closures
that unit creates before it binds $`C`$, as the class's own binding
$`C^{\mathit{self}}`$ (`C.[[self]]`), which the initialization unit $`I`$ reads
the way a function reads a module constant:

```math
\frac{\mathtt{const}\ C{:}K_C=\mathtt{ctor}\ldots\in I}
     {\Gamma_I(C^{\mathit{self}})=⟦K_C⟧}\ \textsf{class-self}
```

The unit checks the class value against $`K_C`$, its construct signature and
its static fields, where it binds $`C`$, after the static field initializers,
and nothing reaches $`C^{\mathit{self}}`$ before: only those closures read it,
its static methods among them, and none runs until an instance or the class
value exists, but a static method whose body does not read the class, which a
static initializer may call, and a constructor reading no class and running no
code, through which one may construct the class ([classes](SOURCE-CONTRACTS.md#classes)).

## Source closures and their annotations

A source closure `(x₁: D₁, …, xₙ: Dₙ): Rₛ => t` is checked at the arrows its
claim names, by the creation rule of [Callables](CALLABLES.md#typing-rules): each claimed
arrow $`(R,\vec A,B)`$ types the body at its own receiver, its first $`n`$
parameters and its result. The source adds two requirements. Each claimed
parameter is within the annotation's, $`A_j\sqsubseteq_G D_j`$ for $`j\le n`$
(`within`), and, where the source states a result, the body meets it at the
annotated signature (the `closure-result` obligation):

```math
\frac{\forall(R,\vec A,B)\in L.\;\bigl(\forall j\le n.\;A_j\sqsubseteq_G D_j\bigr)
        \land\;\Gamma,\mathit{this}{:}R,\vec x{:}\vec A_{\le n}\vdash_G t:B
      \qquad
      R_s\neq\bot\;\Rightarrow\;\Gamma,\mathit{this}{:}Q_s,\vec x{:}\vec D\vdash_G t:R_s}
     {\Gamma\vdash_G \bigl(\vec x{:}\vec D\bigr)\colon R_s\Rightarrow t\;:\;\bigwedge L}
```

with $`R_s=\bot`$ for a closure whose result the source leaves out (the
Fragment's `result` is `null`) and $`Q_s`$ the receiver the source states (`top`
for an arrow). The premise over $`L`$ is the creation rule's, so leaving the
result out drops a requirement and no check: the result is the claim's, like
any expression's. A parameter written without a type has for $`D_j`$ the type
TypeScript gives it from its context, which the parser writes
(`closureParamType`) as an annotation of it would read: primitives,
literals, unions, intersections, arrays, type parameters, declarations by
name, and tuples of required positions and a rest, readonly as TypeScript
types them. A tuple with an optional position is refused, since TypeScript
gives that position's type with `undefined` whether or not an annotation
wrote it (`invalid-contextual-optional-tuple`). It is a proposal like any claim, since the body is checked at
$`A_j\sqsubseteq_G D_j`$ and the closure at $`\bigwedge L`$ wherever it goes, the
call offering it included. A closure is **offered** each signature binding
more parameters than it does that is expected where it flows: passed where
a callback is offered more parameters (`xs.reduce(acc, null)`), bound under
such an annotation directly or through another binding, returned at such a
result. It is claimed where it is created at that signature beside its own,
and its code is checked at each (`CodeOffers`), the premise over $`L`$ above
keeping each claimed parameter within its annotation:

```math
\frac{\lambda(\vec x{:}\vec D).t\ \text{flows to a position expecting}\ (R;\vec A)\to B\quad |\vec x|<|\vec A|}
     {(R,\vec A,B)\in L}\ \textsf{offer}
```

Written and contextual parameter types use the same source type language and
annotation admissibility checks. Scope checking traverses every type
constructor, including reference arguments and generic method binders. Named
contextual types enter the declaration graph by declaration identity, with the
same dependency collection and declaration validation as written references.
Intersection meaning belongs to the shared semantic lowering.

A closure is offered a variadic signature too, `process.on(sig, shutdown)`
at `(...args: unknown[]) => void`, when its parameters are among the
signature's fixed ones: $`L`$ then holds that signature's fixed row
(`offerRows`), and each claimed parameter is within the annotation's as for
any row. A signature binding no more parameters than the closure does is no
offer: a closure binding an optional second parameter, held at a
one-parameter annotation, is not claimed at a two-parameter signature it
later flows to, and its binding there is only that annotation. A `void` result is $`\top`$, so a closure returning a promise meets it.
No subtyping widens an arrow's parameters: a value typed `() => undefined` is
not a variadic callback, only a closure literal is created at one.

A class is the same case reached from a construct signature. Its methods are
closures with the instance as receiver, and its value is construct-only code
allocating the instance from them. Where the class value is expected at
$`\mathsf{new}()\Rightarrow I`$ whose instance $`I`$ has a member $`m`$ at
$`(\vec Q\,\vec U)\to D`$ while the class's method $`m`$ takes $`\vec Q`$, the method's
closure is claimed at $`(C;\vec Q\,\vec U)\to B`$ beside its own $`(C;\vec Q)\to B`$, with
$`C`$ the class's instance type, and the class value at $`\mathsf{new}()\Rightarrow I`$
beside $`\mathsf{new}()\Rightarrow C`$. The creation rule checks the method's
code at both, and `ctorGraph` the constructor's at both, so the instance it
allocates, holding the method as a field of the longer signature, meets $`I`$'s
member by `CoversByFunction`:

```math
\frac{\Gamma\vdash_G \lambda\vec x.t:\bigl((C;\vec Q\to B)\land(C;\vec Q\,\vec U\to B)\bigr)
      \quad\Gamma,m{:}F\vdash_G \{m{=}m\}:C\quad\Gamma,m{:}F\vdash_G \{m{=}m\}:I}
     {\Gamma\vdash_G \mathsf{class}\{m(\vec x)\{t\}\}:\mathsf{new}()\Rightarrow C\land\mathsf{new}()\Rightarrow I}
```

with $`F`$ the method's claimed type. Nothing here is a new rule: the premises
are the creation rule, `alloc` and subsumption under each construct signature.

The constructor is offered the same way. Where the class value is expected at
$`\mathsf{new}(\vec P\,\vec V)\Rightarrow I`$ while its constructor binds
$`\vec x{:}\vec D`$ with $`|\vec x|=|\vec P|`$, the class value is claimed at
$`\mathsf{new}(\vec P\,\vec V)\Rightarrow I`$ beside
$`\mathsf{new}(\vec D)\Rightarrow C`$ (a resource class constructed with the
request's parameters it ignores: `{ add: Add }` at
`ResourceClass<Collections, Json>`, `new (params: Json) => Resource<Collections>`).
`ctorGraph` checks the code at the first $`|\vec x|`$ parameters, $`\vec P`$, and the
source requires each within the constructor's annotation, as for a closure:

```math
\frac{\forall(\vec A,B)\in L.\;|\vec x|\le|\vec A|\;\land\;
        \bigl(\forall j\le|\vec x|.\;A_j\sqsubseteq_G D_j\bigr)\;\land\;
        U,\vec x{:}\vec A_{<|\vec x|},\Gamma\vdash_G b:B
      \qquad U,\vec x{:}\vec D,\Gamma\vdash_G b:C}
     {\Gamma\vdash_G \mathsf{class}(\vec x{:}\vec D)\{b\}:\bigwedge L}
```

with $`C`$ the class's instance type, its own signature
$`\mathsf{new}(\vec D)\Rightarrow C`$ among $`L`$. A constructor needing more than
the offered parameters meets no such signature, and the value holding it is
refused: a class whose constructor calls its parameter's `toString` is not a
`new (params: Json) => Resource<C>`, as a Json object may own that key at any
Json (`invalid-collections-json-constructor.ts`).

### Sloppy code reading `this`

A function whose code is sloppy and reads `this` (its body, a default or a
nested arrow) binds its receiver as a sloppy call does: an object unchanged,
any other converted. Its code's kind is `sloppy`
([graph code](SEMANTICS.md#graph-code)); every other ordinary function's is
`call`. With $`\mathrm{obj}_G(R)`$ for a receiver type of clause rows each an
object clause (`kindOffers`), a sloppy closure reading `this` has a receiver
annotation $`Q_s`$ and claimed receivers of objects only, and a sloppy module
function reading `this` has a `this` annotation of objects only:

```math
\frac{\mathrm{obj}_G(Q_s)\qquad\forall(R,\vec A,B)\in L.\;\mathrm{obj}_G(R)}
     {\lambda\,\mathit{this}{:}Q_s,\vec x{:}\vec D.\,t\ \text{has kind}\ \mathsf{sloppy}\ \text{at}\ \bigwedge L}
\qquad
\frac{\mathrm{obj}_G(Q)}
     {\mathsf{function}\ f(\mathit{this}{:}Q,\ldots)\ \text{sloppy, reading}\ \mathit{this}\ \text{is admitted}}
```

A module function's `this` is an input assumed at $`Q`$, so a caller passes an
object, which the sloppy call binds unchanged. Other receiver types are
refused ([model limits](SOURCE-FRAGMENT.md#model-limits)).

### Calls through `Function.prototype.call`

`f.call(r, ā)`, `f.apply(r, l)` and `f.bind(r, ā)` are the standard methods
where `f` is a known local function, $`\mathrm{fn}(f)`$; a function a caller
supplies may own a `call` property. With $`\mathrm{vals}(x)`$ the values a
local $`x`$ may hold, a `const`'s initializer, or a `let`'s initializer and the
right side of each plain assignment to it in its block (none where another
form writes it or a declaration in its block shadows it), and
$`\mathrm{mem}(o,m)`$ what an object literal $`o`$ holds at $`m`$ once built,
read from its last part giving $`m`$, a spread giving what its source gives:

```math
\frac{f\ \text{an arrow or a function expression}}{\mathrm{fn}(f)}
\qquad
\frac{\mathrm{vals}(x)\neq\varnothing\quad\forall v\in\mathrm{vals}(x).\;\mathrm{fn}(v)}{\mathrm{fn}(x)}
\qquad
\frac{m\ \text{written by no assignment in the file}\quad\forall o\in\mathrm{vals}(x).\;\mathrm{mem}(o,m)\ \text{a known local function}}
     {\mathrm{fn}(x.m)}
```

beside a module function declaration with a body, an `Object.assign` callable
and a `.bind` of a known local function (`localArrow`). A spread copies a
literal's own enumerable data properties, so the copy's member is the
source's.

A name means the declaration it resolves to, lexically (`resolve`): the
nearest enclosing scope binding it, a loop's or a `catch` clause's binding
included. A file-level function is known when not exported: an exported one is
held by every importer, where other code may give it an own `call`. A
script's top-level function is also a property of the global object, which
the trusted assumption that other code preserves the file's top-level
bindings and their functions' `call`, `apply` and `bind` covers (other code
may still read it) ([trust surface](DESIGN.md#trust-surface)). Every value these rules follow is confined (`confined`): the
locals they read and the file's function declarations they reach. Each
reference to one is the callee of a call, the object of `.call`, `.apply` or
`.bind`, directly or through one member, the target of a plain assignment to
it, the object of a read or write, not a call, of a member other than `call`,
`apply`, `bind` and the members followed, or a local's value: a local's
initializer or the right side of a plain assignment to it, the reference
itself or a spread or member value in an object literal that is. That local is
confined in turn, the member it is given at is followed, and a literal it is
given has no accessor, which a spread runs with the object as its receiver.
Code holding a followed value is then the file's own, whose writes the rules
above read: any other reference (an argument, `Object.assign`'s target, a
method call's receiver, a return, a read of a followed member) and an export
may hand it to code that replaces its member or gives the function an own
`call`.

## Certifying inferred call effects

**Definition certification and initial producer inference are implemented;
native overloads and graph composition, including fixed qualified calls, are implemented.** The semantic foundation is
[the qualified arrow equation](SEMANTICS.md#effect-qualified-call-contracts).
Definition checking and application both carry the effect;
changing only the native `map` declaration would introduce a trusted assumption
about client code.

Write $`\Gamma\vdash e:B\;!\epsilon`$ for safety with the entry-relative
postcondition $`Q_\epsilon`$ from that equation. Semantically this quantifies over
every eligible budget, world, heap $`h`$ and environment satisfying $`\Gamma`$, and
requires `SafePost B (Qε h)` for the instantiated term. It is not a Boolean
producer judgement and does not mean “no write syntax occurs.”
For a fixed-arity closure, the intended introduction rule is schematically

```math
\frac{\Gamma_c,\mathit{this}:R_c,\vec x:\vec A
             \vdash b:B\;!\epsilon}
 {\Gamma_c\vdash\mathrm{closure}(\vec x,b):
             \mathcal F_\epsilon(R_c,\mathrm{ArgsShort}(\vec A),B)}.
```

Here $`\Gamma_c`$ describes the actual captured values and fixed storage
contracts, not transient captured-cell observations. The premise ranges over
all admitted arguments and future calls. Existing source-annotation checks,
code arity/binding checks and the ordinary body-safety obligation remain.
Parameter defaults execute on invocation, so their effects are included; rest
allocation is allowed. An overload needs the premise for each claimed qualified
signature, and a scheme needs it for every admissible binder assignment, not
just observed instances. These are obligations on the eventual graph certificate,
not permissions to omit those forms from its accounting.

Application uses that type alone. With callee, receiver and arguments already
values, its intended rule is

```math
\frac{\Gamma\vdash f:\mathcal F_\epsilon(R_c,\mathcal A,B)
 \qquad\Gamma\vdash r:R_c\qquad\Gamma\vdash\vec v:\mathcal A}
 {\Gamma\vdash\mathrm{invoke}(f,r,\vec v):B\;!\epsilon}.
```

The effect's entry heap is the heap **after** evaluating the callee, receiver
and actual expressions. Their evaluation may mutate state; it needs its own
composition proof. A call-site rule must not inspect the callback body. Named,
returned and imported callbacks are handled by the same rule whenever their
qualified type is established. Calls inside a checked body in turn consume
their callees' qualified types; higher-order effect requirements are types too.

Forgetting an effect is valid, and manufacturing one by subsumption is not.
The coverage condition, in addition to the usual domain contravariance
and result covariance, is

```math
\frac{R'_c\le R_c\quad\mathcal A'\subseteq\mathcal A\quad B\le B'
 \quad\forall h,h',v.\;Q_\epsilon(h)(h',v)\Rightarrow Q_{\epsilon'}(h)(h',v)}
 {\mathcal F_\epsilon(R_c,\mathcal A,B)
       \le\mathcal F_{\epsilon'}(R'_c,\mathcal A',B')}.
```

In particular, heap-preserving entails unrestricted, but the converse has no
rule. Normalization and substitution must carry the effect per signature.
No per-function global flag can justify a stronger effect on another overload.

For native `map`, the built-in ordinary-construction invariant supplies the
construction premise. A dense receiver and a heap-preserving callback produce
no holes, so the qualified overload can promise the source-readable result
`U[]` at every `U`. The allocation chooses that lifetime store contract; it does
not force the stronger dense contract onto the result's writable store location.
The unrestricted overload promises a sparse result. Both use ordinary selection and application;
there is no body-inspecting `map` rule. `find`/`findIndex` similarly consume a
qualified callback accepting `T`, or an unrestricted one accepting `T | undefined`.
An explicitly submitted stronger effect
claim must fail with a located obligation rather than silently disappear.

The semantic introduction and elimination rules are proved in
`ProgramTyping.callsT_of_graph`, `restsT_of_graphRest`, and `CallEffects.call_safe`.
`GraphCode.codeChecked_sound` checks ordinary safety and the signature's effect
together; a separate unqualified body check cannot introduce a qualified type.
Rest-collecting entries retain their store contract in the checked frame, and
the entry allocation preserves the input heap before the checked body runs.
The effect algorithm ([ExpressionEffects.lean](../lean/Verification/Programs/ExpressionEffects.lean))
admits a node whose expression is an **inspection**: a term built from slots,
values, immutable lets, tests, conditionals, operators, throws, lengths, field
and element reads, and allocations whose initializers are slots or values,

```math
\begin{aligned}
o &::= x \mid v\\
i &::= o \mid \mathsf{let}\ x=i\ \mathsf{in}\ i \mid \mathsf{test}_k(i) \mid \mathsf{if}\ i\ \mathsf{then}\ i\ \mathsf{else}\ i \mid i \oplus i \mid \mathsf{throw}\ i \mid \mathsf{len}(i) \mid i.f \mid i[i] \mid \mathsf{make}_c(\vec f;\vec o) \mid [\vec o]
\end{aligned}
```

```math
\frac{\Gamma\vdash i:B\qquad i\ \text{an inspection}}
 {\Gamma\vdash i:B\;!\;\emptyset}\ \textsf{inspect}
```

with the premise the node's ordinary typing. No step of an inspection writes a
location it did not allocate: a read gives the value its location holds and an
allocation appends fresh locations, so from a heap holding values each step
keeps the heap a prefix and leaves an inspection (`Purity.inspect_step`). Every
heap meeting an admissible world holds values (`HeapExpressionRules.heap_values`),
and the ordinary safety derivation supplies such a world at every step, so the
rule's conclusion holds (`ExpressionEffects.inspect_safe`). A member read off a
primitive is an inspection: the conditional on the primitive's shape, the fresh
wrapper whose `[[proto]]` is the prototype slot, and the read through it.
`ControlFlow.state_progress` is shared
with ordinary safety, so the additional graph proof has no second set of edge or
branch rules. During expression evaluation, `GraphCode.ReturnsPost` tracks the
normal-return postcondition independently of the safety proof's evolving world.
A caught exception cannot use that postcondition: compositional checking refuses
handlers, while the independent pure-graph rule still admits pure handlers.
Fixed calls use `ExpressionEffects.selectedCall_sound`: the selected application
rule's footprint must lie within the bound, and its operands must already be values.
The proof consumes `CallEffects.call_safe`, including padded missing arguments;
a result-subtyping derivation retains the same postcondition. It never inspects
the callee's implementation. Pure immutable lets also compose: $`\mathsf{Pure}(a) \land \mathsf{Pure}(b)`$ implies $`\mathsf{Pure}(\mathsf{let}\ x=a\ \mathsf{in}\ b)`$.
[Purity.lean](../lean/Verification/Semantics/Purity.lean) checks purity; its `pure_subst` proves preservation under the value substitution at the
binding step; instantiation respects bound variables at every binder depth.
This covers the nested lets introduced by pure coalescing and logical operands.
Other call forms and nested heap operations remain conservative.

`PromiseWith.combine` retains both premises' effects when combining result
guarantees (the effect meet, so either premise can supply heap preservation). Both promises concern the same admitted calls; determinism gives
the same resulting heap, while the ordinary cross-world compatibility premise
still governs the result type. No effect can arise solely from combining
unrestricted results. `PromiseWith.bound` is the common forwarding proof for
fixed and variadic binding: saving a receiver and prefix changes the admitted
arguments, not the forwarded call's heap guarantee.

This checker is wired into source acceptance, including
`SourceClaimJson.checkJson_safe`. One contract record carries receiver,
arguments, result and required effect through graphs, claims and certificates;
subtyping checks effect implication and substitution preserves it. Ordinary
source annotations remain unrestricted; OCaml proposes preservation for
closure bodies of reads, element reads, fresh allocations, patterns without a
rest, and fixed calls and method calls whose callee's signatures all state it
(`heap_preserving_expr`), retaining it through symbolic claims and substitution.
Broader composition remains implementation work. Evidence production adds a
code entry to its search table only after the complete body/effect check passes.
A forged effect thus fails at the defining callable's located typing obligation.
All code certificates remain in the submitted response, and final acceptance
independently checks every one; withholding a search hint cannot hide a failure. Qualified graph claims can
already be submitted and certified through the ordinary source pipeline.

**Function declarations.** A declaration's claim states the closed
footprint $`\Phi`$ proposed for its signature (`footprint` in the
[claims](SOURCE-CLAIMS.md)). The unit of a declaration claiming a footprint
other than `all: any` is checked as a code entry's graph is: its nodes pure,
or each node within $`\Phi`$ on normal return (`effectResult`, alongside
ordinary safety), for a plain result under the ordinary checker. A node is
within $`\Phi`$ as an inspection, which preserves the heap; as a write of a
field every alternative of the object's type gives a type of source values,
within `{value: any, store: keep}` since the location holds a value
(`ExpressionEffects.write_within`); or as a fixed call at a selected signature
whose footprint is within $`\Phi`$. Runs within a closed footprint compose
(`Closed.Holds.trans`), so the graph is (`GraphCode.goto_bounded`). A guard,
an assertion function and a unit qualified by a resolution descriptor are
refused such a claim. A code entry's signature follows the same rule
(`GraphCode.effectCheckedResult`). With $`P`$ the unit's graph, $`\Gamma`$ its
inputs and $`B`$ its result,

```math
\frac{\vdash P:\Gamma\to B\qquad \forall l.\ P_l\ \text{pure, or within}\ \Phi}
     {\vdash P:\Gamma\to B\;!\;\Phi}\ \textsf{declaration-effect}
```

and `SourceClaimJson.checkJson_safe` states, for each such unit, that its
graph run as code from inputs it admits returns with a heap its claimed
footprint relates to its entry heap (`SourceExtraction.checkRequests_footprint_at`).
Every other unit reads the declaration at its annotation's signature stating
that effect, its variadic extension included (`moduleArrow`), as it reads the
declaration's ordinary signature: that each declaration meets the signature
the others read it at is the [module composition](../WORK.md#module-composition)
argument. A parameter default executes in the declaration's graph, so the
check covers it. An imported function is read at its declaration's type,
which states no effect (`invalid-preserving-callback-value-import`). OCaml
proposes the effect at the greatest fixpoint over the module: every
declaration whose body could preserve the heap, were its callees to, is
assumed preserving, recursion included, and rounds of inference withdraw the
assumption from each whose claims then do not show it; a body calling a
quantified callee at an instance is not proposed. A forged effect fails at
the first node that does not preserve the heap, in evidence production and
in checking (`declaration-preserving-callback`,
`invalid-declaration-write-callback`).

## Parameter initialization order

The source adapter also performs acyclic closure conversion for literal
closures capturing later parameters. `Fragment.parameterOrder` delays only
closure allocations, until their dependencies are initialized; no executing
initializer may read or expose a pending closure. Potentially effectful defaults
keep their relative order. A closure is allocated once and captures initialized
immutable parameters and unchanged outer cell identities. This preserves
sharing and observations up to renaming fresh locations. Cycles and pending
closure exposure are refused. This source-correspondence argument remains in
the trusted adapter; it is not claimed as a Lean proof about JavaScript.
The same schedule orders a code's entry nodes, a default's evaluation among
them. No heap location changes its fixed world type.
