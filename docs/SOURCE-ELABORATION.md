# Source elaboration

Source verification requires evidence for the core judgments and a lowering of
source operations that preserves their meaning. This document specifies that
evidence search and the lowering of every source form: derived forms,
statements, guards, iteration, patterns, mutable bindings, closures, the
certification of inferred call effects and parameter initialization.

The prerequisites are the expression, graph and heap judgments in
[Program typing](PROGRAM-TYPING.md), the operational language and worlds in
[Semantics](SEMANTICS.md), and graph types and checked subsumption in
[Positive types](POSITIVE-TYPES.md). Types are finite unions of graph labels;
$`\Gamma`$ assigns types to variables, and $`\Gamma\vdash_G t:A`$ is the core
judgment for a term $`t`$ in graph $`G`$. Supplied point claims fix a graph node's
entry context and expression result type; every incoming edge must justify that
context. Declaration and library contracts used by lowering are specified in
[Source contracts](SOURCE-CONTRACTS.md). The source fragment and refusal
boundaries are specified in [Source fragment](SOURCE-FRAGMENT.md).

## Adding a source form

A source form the fragment does not admit enters it with all of the
following, in one change:

1. **The parser's gate.** The parser admits the form only where it is
   lowered faithfully, and refuses every other occurrence with a located
   reason (`tools/fragment-*.mts`, `type-term.mts`).
2. **The Fragment wire.** Each field the form carries is declared in
   [the Fragment format](FRAGMENT-FORMAT.md) and decoded by Lean field by
   field; `node tests/json-field-names.mts` checks the field names agree.
3. **The lowering.** The form's lowering is stated here, as a derived form
   or a rule, with JavaScript's evaluation order and binding scope. It
   emits its checks as located obligations and reuses an existing rule
   rather than adding an approximate one. A new
   executable field on an existing constructor is audited on every lowering
   and certification path: each path executes it or refuses it, located.
4. **Claims and labels.** Whatever the producer claims about the form is
   in [the claims wire](SOURCE-CLAIMS.md), and Lean checks it.
5. **The refusal index.** Each part of the form that stays refused has a row
   in [the fragment boundary](SOURCE-FRAGMENT.md#fragment-boundary): the
   construct, the reason, the owning section and the cases.
6. **Cases and controls.** Positive and negative pipeline cases
   (`pipeline/cases.mts`), and forged-claim controls (`pipeline/test.mts`)
   for which program point a claim attaches to, which no proof covers.
7. **A Node counterexample.** Each negative case whose refusal guards
   JavaScript behaviour runs under Node (`tests/node-runs.mts`) and shows
   the behaviour the refusal excludes.

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
body under the parameters the code takes, followed by captures.

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
concern expression evidence; program acceptance and its safety implication
([what "verified" means](DESIGN.md#what-verified-means)) remain the semantic
boundary.

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

### Known conditions, ternaries and nullish coalescing

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

### A comma in a test position

A comma in a test position is a derived form too: its left operand runs for
its effects, and its right operand is the condition, lowered in the state
the left operand leaves, its refinements on both edges; an exception of the
left operand is the comma's. `(a, b) && c`, `(a, b) || c` and `!(a, b)` run
`a` first and are then `b && c`, `b || c` and `!b`:

```math
\frac{\Gamma\vdash a \Rightarrow \Gamma' \quad \Gamma'\vdash_R\ \mathsf{if}\ (b)\ S_1\ \mathsf{else}\ S_2}
     {\Gamma\vdash_R\ \mathsf{if}\ ((a\mathtt{,}\ b))\ S_1\ \mathsf{else}\ S_2}\ \textsf{if-comma}
```

with $`\Gamma\vdash a\Rightarrow\Gamma'`$ the context the left operand's
evaluation leaves, an earlier fact it may invalidate gone
(`comma-test-refinement`, run under Node).

### Shadowing

JavaScript's scopes nest; the lowering's are lists of
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

### Default imports

`import x from M` binds `x` to the export of $`M`$
named `default` ([ECMA-262](REFERENCES.md#ecma-262)'s ImportedDefaultBinding),
as `import { default as x } from M` does, and is read as that named import:

```math
\frac{\Gamma(\mathtt{default}@M)=T}{\Gamma(x)=T}\ \textsf{default-import}
```

`export default function f` exports $`f`$'s own binding as `default`, which
no code of an imported module may write, so its unit is certified as a named
export's is (`default-import-value-import`). An import binding no name
(`import "m"`) runs the module for its effects alone and is refused.

### Namespace imports

A module namespace object's members are the module's
export bindings, read as an import binding reads them
([ECMA-262](REFERENCES.md#ecma-262)). So in `import * as ns from M`, where
every mention TypeScript binds to `ns` is a member read `ns.x` or a qualified
type name `ns.T`, each member is a binding of the file, named `ns.x`, which no
identifier spells, bound to the export of $`M`$ that TypeScript binds the
member to, as a named import of it is:

```math
\frac{\mathrm{mentions}(ns)\subseteq\{\,ns.x_1,\ldots,ns.x_n\,\}\quad \Gamma(x_i@M)=T_i}
     {\Gamma(ns.x_i)=T_i}\ \textsf{namespace-import}
```

A read of `ns.x` is a read of that binding, at its own span and spelling,
and a qualified type name `ns.T` names the declaration the export is; a
member used only in types imports no value. A refusal about a member names
its use (`namespace-members.mts`; the declaration graph resolves each
member through the checker). A call `ns.f(a)` passes the namespace object as
the receiver, where a call of the binding passes `undefined`; the two agree
for a callee whose signatures state no `this` parameter, and a call of one
that does is refused where it is written. Any other mention of `ns`
(`const m = ns`, `ns[k]`, `ns?.x`, `{ ns }`, an export) is refused at the
mention, and so is a write of a member, which JavaScript refuses with a
`TypeError`.

### A `let` nothing assigns

A `let` statement whose bindings are all
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
its initial value is. Such a pattern in a `for` head is refused. A written `let` held in a cell
([slot or cell](#mutable-bindings-and-module-constants)) that holds a union of objects is
not narrowed by a test of its object (a cell's known contents are primitive
values, or that it holds no `undefined`, and a write between the test and the
read may replace it); a read of a member only some arms state is refused
with that reason.

### Shorthand properties

A shorthand property writes the value its name
reads, as the field of that name, the name resolved as any read of it (a
shadowing local's renaming, above, included):

```math
\{\ldots,\ x,\ \ldots\}\;\equiv\;\{\ldots,\ x\colon x,\ \ldots\}
```

### Angle-bracket assertions and empty statements

`<T>e` is `e as T` and `<const>e` is `e as const`,
the same assertion (an obligation on the operand, never a fact); a
top-level `;`, as one in a body, is nothing.

### `instanceof`

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
immutable variable is refined as by every tag test ([guards](#guards)).

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

### Optional chains

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

with $`T_q`$ the nullish tag's slices. Every chain binds the one variable
$`\mathsf{chain}`$, so in `a?.b?.c` the outer chain's binding shadows the
inner's. A test's lowering reads a saved value through the expression it was
saved from (its origin) only where every name that expression mentions
still denotes the binding it was recorded with; a mention of the inner
$`\mathsf{chain}`$ is not read as the outer one, and is left as the saved
value itself (`optional-chain-element-receiver`). The body is checked where the saved
receiver holds its present slice, so a method called through the chain
(`o?.m()`) has the present `o` as its receiver. `o.m?.(a)` tests the member
read once, `o.m`, and calls it with `o` as its receiver (ECMA-262's
OptionalChain: the reference's base is the call's `this`), the arguments
evaluated only where the member is present:

```math
o.m\,?.\,(\vec a)\;\equiv\;\mathsf{let}\ \mathsf{chain}=o.m\ \mathsf{in}\ \mathsf{if}\ \mathsf{nullish}(\mathsf{chain})\ \mathsf{then}\ \mathsf{undefined}\ \mathsf{else}\ \mathsf{chain}.\mathtt{call}(o,\vec a)
```

The chain saves the tested value, and the receiver is read again: `o` is
`this` or a name whose read cannot throw nor run code (`readCannotThrow`) and
that the file assigns nowhere, so the second read gives the value the first
did (`optional-method-call`, run under Node). A member at a computed key
(`o[k]?.()`), any other object (`f().m?.()`, a name the file assigns) and
spread arguments are refused (`optional-method-call-object-refused`). On a `null` or `undefined` literal receiver the
chain is `r, undefined`: the literal is the receiver's whole value, and the
body never runs.

A chain compared with a literal, `x?.p ⊙ c` or `c ⊙ x?.p`, with $`\odot`$
one of `===`, `!==`, `==`, `!=`, $`c`$ a literal, $`x`$ `this` or a name
the file binds outside an ambient context (`inertRead`), and $`.p`$ one or
more named reads, is the test of the receiver, then the comparison of the
receiver's reads (`chainComparison`):

```math
x\,?.\,p\ \odot\ c\;\equiv\;
\begin{cases}
x\ \texttt{!=}\ \texttt{null}\ \ \texttt{\&\&}\ \ x.p\ \odot\ c & \text{where } \texttt{undefined}\odot c \text{ is false}\\
x\ \texttt{==}\ \texttt{null}\ \ \texttt{||}\ \ x.p\ \odot\ c & \text{where } \texttt{undefined}\odot c \text{ is true}
\end{cases}
```

`undefined === c` holds where $`c`$ is `undefined`, `undefined == c` where
it is `null` or `undefined`, and `!==`, `!=` are their negations. Both
sides have one value: where $`x`$ is nullish, the chain is `undefined` and
the comparison is $`\texttt{undefined}\odot c`$, which is the value the
right side's first operand decides; elsewhere both are $`x.p\odot c`$. The
right side reads $`x`$ twice. A read of a binding the file declares, or of
`this`, runs no code, and between the two reads only the nullish test runs,
which runs none either, so they read one value; the literal's evaluation
runs nothing. A global the file only declares may be an accessor of the
global object, which answers each read anew, so its chain stays a value
(`invalid-optional-chain-test-ambient`). The tests then name $`x`$ and its field,
which refine as every test of a name and of a field of a name does
([guards](#guards)): where `b?.k === "d"` holds, `b` is
present and at the arms whose `k` may be `"d"`; where it fails, nothing is
known of `b`. A comparison with another operand (a name, which may itself be
`undefined`), a receiver other than a name, or a link other than a named
read is the chain's value compared, which refines nothing
(`optional-chain-test`, `invalid-optional-chain-test-*`, each run under
Node).

### `typeof` as a value

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
with a shape's literal stays the one tag test ([guards](#guards)).

### `in`

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
(`inKeyRefusal`, [guards](#guards)). The operand's clauses are
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
\%\mathsf{HasProperty}\%:(\mathtt{string}\mid\mathtt{number}\mid\mathtt{symbol},\ \mathtt{object})\Rightarrow_{\emptyset}\mathtt{boolean}
```

The call evaluates the key, then the object, then the lookup, as `in` does;
converting the key runs no code, and neither does the lookup on the objects
a program holds (no proxy, [trust surface](DESIGN.md#trust-surface)), which
writes nothing: the signature states the empty footprint, so a callback
testing a key keeps a `map`'s result dense (`library-preserving-reflection`).

### Reads at a union of key singletons

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

### Logical operators

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

### Conditions read for truthiness

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

### A guard's Boolean return

In a type guard or an assertion function, a `return` of a Boolean by its
form (a shape, key, instance or equality test, a family guard's call, the
test of its argument's tags ([a guard on any argument](HOST-FAMILIES.md#a-guard-on-any-argument)),
a negation, a comparison, or `&&` and `||` of such)
returns its truth's Boolean, a condition:

```math
\mathsf{return}\ e\;\equiv\;\mathsf{if}\ (e)\ \mathsf{return}\ \mathsf{true};\ \mathsf{else}\ \mathsf{return}\ \mathsf{false}
\qquad (e\ \text{Boolean by its form}).
```

The equation holds of JavaScript's evaluation: such an `e` evaluates once to
`true` or `false`, which is its truth. The guard's promise is then checked
where it returns `true`, in the context the test's answer leaves, as a
statement `if` narrows; returning the joined value would check it where the
test's answers have joined. An arrow's expression body is such a `return`.
The parser writes the literals at the first two code units of the `return`
keyword (an arrow's `=>`), which no expression has, each the span of its own
`return` (`booleanReturn`), and the producer claims them as it claims any
literal (`guard-boolean-return`, `invalid-guard-boolean-return`).

### Negated operands

A negated left operand that is no test, `!a`, is a dispatch on `a` itself,
its arms exchanged, and a left operand that is the same operator's
application is regrouped:

```math
\begin{aligned}
\mathsf{truth}(!a\mathbin{\Vert}b)&=\mathsf{if}\ \mathsf{truthy}(a)\ \mathsf{then}\ \mathsf{truth}(b)\ \mathsf{else}\ \mathsf{true},\\
\mathsf{truth}(!a\mathbin{\&\&}b)&=\mathsf{if}\ \mathsf{truthy}(a)\ \mathsf{then}\ \mathsf{false}\ \mathsf{else}\ \mathsf{truth}(b),\\
\mathsf{truth}((a\mathbin{op}b)\mathbin{op}c)&=\mathsf{truth}(a\mathbin{op}(b\mathbin{op}c)).
\end{aligned}
```

Each equation holds of JavaScript's evaluation: `!a` is `true` exactly where
`a` is falsy, `||` evaluates its right operand exactly where its left is
falsy and `&&` where it is truthy, and grouping the same operator either way
evaluates the operands once each, left to right, and stops at the same one.
So `a` is evaluated once, then `b` exactly where `!a` does not decide, and
the truth is the operator's. The decided outcome is a literal, `true` for
`||` and `false` for `&&`, at the span of the `!` (`negationMark`), which no
source expression has: the producer claims it there for every negated
operand of `||` or `&&` that is no test, a right one's included, which
regrouping makes a left one (`ExpressionPlan.truthOf`, `Claims.Sites`). The
arm where `a` answered `true` is the arm a guard call narrows on, so
`if (!isRecord(v) || n > 3) throw …; return v` reads `v` at the promised
type, a closure in the right operand included
(`guard-negated-short-circuit`); the outcome `!g(v) && b` false promises
nothing (`invalid-guard-negated-and`).

<a id="a-negation-of-tests"></a>
A negation of tests, `!(a || b)` or `!(a && b)`, is evaluated as a value:
its operand's dispatch, then the negation of the value each arm leaves.
A condition then dispatches on the predicate each arm leaves, its arms
exchanged. The negation's claim is checked where the evaluation computes
it, and each read the dispatch makes again by the dispatch's own node, with
the knowledge its incoming edge carries: where `k.name === "a"` failed, the
fact that `k.name` holds the rest of its literals types the next read of
`k.name`, which the declared field does not. A negation whose operand's type
answers its truthiness one way, $`q`$, proposes the part of its claim $`A`$
answering the other way as the node's type (`decidedNegation`):

```math
\Gamma\vdash a:B,\qquad \text{every clause of }B\text{ answers }q,\qquad T_{\neg q}(A)\neq\emptyset
\qquad\Longrightarrow\qquad
\text{proposed type }T_{\neg q}(A).
```

The node `if a then false else true` must derive this proposed type under
the existing typing rules; the following effect node checks the claim
$`A`$ separately.

In the arm of `!(a || b)` where `a` held, the negation is `false` and
decides the condition there, and no dispatch reaches the true branch from
that arm (`negated-disjunction-test`, each function run under Node). Where
the negation fails, one of the tests held, and where a call, the test's own
operand or a getter may have written the field, its read is not narrowed
(`invalid-negated-disjunction-else`, `-arm`, `-write`, `-operand`, `-getter`
and `invalid-negated-conjunction`, run under Node; forged claims of a
re-read and of the negation refused in search and in checking,
`pipeline/test.mts`).

A slice of the labels cannot refine `unknown`, which no label
decomposes. An arm's entry therefore takes, for each binding its operand
reads, the producer's claim at that read as a candidate, which the incoming
dispatch edge checks under the edge's own observation, as it checks a
statement entry. The read is the binding's first in the arm before any
choice. For a binding that may change, it is the first before any other
operation. A value binding (a parameter, a `const`) holds one value
throughout, so its first read may also follow reads of members, references
and positions, effect-free evaluations, and calls of native intrinsics,
which state no promise. A call of a source function ends the search, since
an assertion function's promise may narrow the binding there. So
`typeof v === "number" && Number.isSafeInteger(v)` reads `v` at `number`
(`logical-narrowing-past-reads`). A read claimed narrower than the edge
establishes is refused when evidence is produced and when it is checked
(the forged operand entry in `pipeline/test.mts`).

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

### Closure branches

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
shared join would.

A block closure that does not return on every terminal arm completes, which in
JavaScript returns `undefined`; its body ends with $`\mathsf{return}\ \mathsf{undefined}`$ at the closing brace, so that the shapes above apply
unchanged, and the result claim must admit $`\mathsf{Undef}`$ (`void` is top). A
bare `return` is the same literal at its keyword.

### Keyed access at a singleton key

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

### Guarded returns

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

## Class forms

A class declaration's reading is [classes](SOURCE-CONTRACTS.md#classes);
the forms below lower a derived class, a class extending `Error`, and
class members.

### Derived classes

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

### A class extending `Error`

The standard `Error`, by its declaration
identity, is a base too: `class Decline extends Error {}`, and `class
DeclarationError extends Error { readonly at: Span; constructor(at, message)
{ super(message); this.at = at; } }`, and a class extending either, to any
depth. JavaScript constructs such an instance in the base: `super(m)` runs
`Error(m)` with the derived class as the new target (ECMA-262, `Error (
message [ , options ] )` and OrdinaryCreateFromConstructor), which allocates
an ordinary object whose `[[Prototype]]` is `D.prototype`, owning a
non-enumerable `message` (`ToString(m)`, where `m` is not `undefined`) and,
in V8, a non-enumerable `stack`; each derived constructor then defines its
own fields on it.

The model states the message on the instance's first link, between the
instance and `D.prototype`, which no copy reaches, as the `Error` overlay
entry's result places it on a prototype object (`library-globals.mts`). One
construction serves the family, at the class's prototype and the message its
base gives:

```math
\mathsf{new}\ D(\vec a)\;\equiv\;\{\texttt{[[proto]]}{:}\,\{\texttt{[[proto]]}{:}\,D.\texttt{[[prototype]]},\ \mathit{message}{:}\,\mu_D\},\ \ldots\textit{base},\ \varphi\}
```

```math
\mu_D=\begin{cases}
\mathsf{\%ErrorMessage\%}(\vec a_B) & B=\mathsf{Error}\\
\textit{base}.\mathit{message} & B\ \text{extends}\ \mathsf{Error}
\end{cases}
\qquad
\mathsf{\%ErrorMessage\%}(m)=m\ ??\ \texttt{""},\ \ m:\mathsf{string}\mid\mathsf{undefined}
```

where $`\vec a_B`$ is what `super` passes, none or the one message, and
$`\textit{base}`$ is the base's construction, as for any [derived class](#derived-classes), absent where $`B`$ is `Error`; its own keys are copied and its links
replaced by $`D`$'s. $`\mathsf{\%ErrorMessage\%}`$ binds a string argument as
it is and an omitted or `undefined` one to `""`, which JavaScript's instance
reads from `Error.prototype.message`. The argument is bound at `string |
undefined` before it defaults, so an argument of another type, which
`ToString` converts (`null` to `"null"`, an object by running its code), is
refused at it. The instance's own keys are its declared fields;
`e.message` reads $`\mu_D`$; `e instanceof D` finds $`\kappa_D`$ on
$`D.\texttt{[[prototype]]}`$ further up; `D.prototype`'s own `[[proto]]` is
`Error.prototype`'s contract (`instanceof Error` stays the intrinsic stating
the Boolean).

The model and JavaScript place the message differently: an own
non-enumerable property in JavaScript, a field of a link in the model (for an
omitted message, `Error.prototype`'s in JavaScript, `""` on the link in the
model). JavaScript's instance also owns a non-enumerable `stack`, which the
model does not state. That the two agree on every admitted observation is the
conclusion of this audit of the operations reaching an instance, given stable
prototypes. Each operation is in one of three groups.

Observations that agree:

- `e.message` and a destructuring `{ message }` read the message, or `""`,
  in both: $`\mu_D`$ on the link.
- `e instanceof D` walks the chain in both, finding $`\kappa_D`$;
  `instanceof Error` is the intrinsic stating a Boolean.
- `Object.keys(e)` and `{ ...e }` see the declared fields in both: the
  message and `stack` are not enumerable in JavaScript, and not own in the
  model.
- `Object.values(e)` and `Object.entries(e)` hand over the values of the
  same own enumerable fields, by the overlay's obligated contracts; evidence
  search finds no derivation of either at an instance holding a prototype
  (observed 2026-10-19).

Observations that differ, abstracted by a broad result type, also admitted:

- `"message" in e` is `true` in JavaScript; it is typed a Boolean.
- `for (k in e)` enumerates the declared fields; its keys are typed strings,
  `%ForIn%`'s contract.
- `Object.getOwnPropertyDescriptor(e, k)` exposes JavaScript's descriptor of
  the own `message` or `stack`; its reviewed contract
  (`library-globals.mts`) is `undefined` or a fresh descriptor whose value,
  getter and setter are `unknown`, which either placement meets; evidence
  search finds no derivation of it at an instance (observed 2026-10-19).

Operations excluded, refused with a location:

- ownness and the prototype: `e.hasOwnProperty`, `Object.hasOwn` and
  `Object.getPrototypeOf`, whose results tell the placements apart;
- serialization: `JSON.stringify(e)`, whose replacer `["message"]` reads the
  message through `[[Get]]`; the parameter is a JSON value, which an instance
  holding a prototype is not;
- members JavaScript's instance or `Error.prototype` holds and the model does
  not state: `e.stack`, `e.toString()`, `D.captureStackTrace`, `super.m(…)`;
- an instance member named `message` or `stack` (a method, a field or an
  accessor), and a parameter property of either name, of a class extending
  `Error` at any depth, refused at the member: JavaScript's own property
  shadows a method, and a field or a parameter property defines or assigns
  the own property where the model would add an enumerable field;
- `super(m, options)`, whose `options.cause` is read through `[[Get]]`, as
  the overlay's `Error` is;
- another library base (`TypeError`, `Map`, an ambient class).

#### Reserved writes

JavaScript keeps an instance's own `stack`
non-enumerable through an assignment, and its own `message` too where the
construction passed one; after `new D()` or `new D(undefined)` the instance
owns no `message`, and an assignment creates an own enumerable one (observed
under Node, `invalid-error-subclass-assign-target`). Either way the model,
which states neither property, would add or change an enumerable own field,
which a later copy, `Object.keys` or an exact-key claim observes. The
restriction is one policy of two parts: a set $`R`$ of reserved keys, here
$`R = \{\texttt{"message"}, \texttt{"stack"}\}`$, and an exclusion of the
receivers that may hold them, here every object owning the prototype key.
Lean's lowering decides it on the claims evidence establishes, at every
write it emits. Notation: $`\mathrm{cl}(T)`$ is the clause list of a claim
$`T`$ when $`T`$ is of clause rows (`plainTy`), its declared names expanded
(`PositiveRules.expand`, then `splitSets`), and undefined for a type with a
parameter or scheme row, which no clause describes.

```math
\mathrm{reserved}(K) \iff \lnot\,\mathrm{plain}(K) \;\lor\; \exists c \in \mathrm{cl}(K).\;
  (c = \mathsf{strLit}\ s \land s \in R)
  \lor (c = \mathsf{strIn}\ S \land S \cap R \neq \varnothing)
  \lor c \notin \mathit{Keyless}
```

```math
\mathit{Keyless} = \{\mathsf{num}, \mathsf{numLit}, \mathsf{numIn}, \mathsf{bigint}, \mathsf{bigintLit},
  \mathsf{symbol}, \mathsf{symbolLit}, \mathsf{bool}, \mathsf{boolLit}, \mathsf{nul}, \mathsf{undef}\}
  \cup \{\mathsf{strLit}\ s, \mathsf{strIn}\ S \mid s, S \text{ outside } R\}
```

```math
\mathrm{protoFree}(T) \iff \mathrm{plain}(T) \land \forall c \in \mathrm{cl}(T).\;
  \mathrm{primitive}(c)
  \lor \bigl(c = \mathsf{dict} \land (\mathit{indexes}(c) \neq [] \lor \mathit{cells}(c) \neq [])\bigr)
  \lor \bigl(c \in \{\mathsf{refs}, \mathsf{dict}\} \land \exists b \in \mathrm{bounds}(c).\ \lnot\, b.\mathrm{admits}(\texttt{[[proto]]})\bigr)
```

```math
\frac{\Gamma \vdash r : T \qquad \kappa = f \ \text{or}\ \Gamma \vdash k : K \qquad
  \mathrm{reserved}(\kappa) \Rightarrow \mathrm{protoFree}(T)}
  {r[\kappa] \mathrel{=} e \ \text{is lowered}}\ (\textsf{Write-Reserved})
```

A key the source spells is reserved when it is in $`R`$; a computed key by
its claim $`K`$. The key domain: a number key converts to its decimal
spelling, never a reserved string; a bigint, a Boolean, `null` and
`undefined` to theirs; a symbol stays a distinct key; a finite template type
reaches the claims as its string alternatives. Any other key claim, an
object's (whose conversion runs code) and `string` included, may be
reserved. A primitive is a clause of `Keyless` or `str`. `top`, `source`,
arrays (whose objects own `[[proto]]` where the graph states the built-ins),
packs and callable clauses are never proto-free; optional fields and
readonly views constrain no absent key and do not make a record proto-free;
a union is proto-free when every alternative is, and an intersection as its
normalization's clauses are. $`T`$ and $`K`$ are the claims at the receiver's
and the key's spans, expression obligations evidence must establish, so the
premise reads certified facts and no TypeScript type or narrowing.

- **Where.** `reservedWriteCheck` (`Lowering/Types.lean`) is called where a
  write is emitted: every graph node whose term is a field write
  (`emitAt`, covering ordinary writes, the saved references of updates,
  logical assignments and destructuring targets, and closures' bodies, which
  are lowered through the same emission), the closed expressions' writes
  (`writeCell`), the key-adding writes of an owned object (`executionGrowth`,
  `growingWrite`, `computedGrowth`), and before any of them in
  `comparisonsExpr`. An array element write's key is a number, never
  reserved. `Object.assign` is the native call's contract check, at each
  source's copy (`mergeObjects`): the source is a write at every key it may
  own, reserved unless every clause of its claim is a primitive or a `refs`
  or `dict` with no index and a key bound admitting neither reserved key.
  A loop head whose target is a member is outside the fragment (the gate).
- **Meaning.** `ProtoFree.clause_sound` proves that no member of a
  proto-free clause owns `[[proto]]`, at every interpretation of the
  clause's operands (any `Ξ`, `X`, `P` of `semWithArgs`), and
  `ProtoFree.list_sound` lifts it to a union of clauses. Refusing more keeps
  `checkJson_safe`; it does not by itself establish that a source write
  corresponds to the model's, which is what the next item argues.
- **Why the premise excludes an instance of the family.** In the model an
  instance owns `[[proto]]` where the fragment builds it: an instance a
  class extending `Error` constructs (its first link), the result of the
  overlay's `new Error` and `Error(m)`, and a value at a class or `Error`
  type, whose declared instance type holds a prototype (`errorInstance` in
  `library-globals.mts`, for constructor results and explicit `Error`
  heritage). A value a unit receives at a dictionary with an index, or at a
  record whose key bound excludes `[[proto]]`, owns no prototype key: that
  is the meaning of those clauses (`dictViewT`, `dictCellT`, `ownKeysT`),
  which the inputs meet by `EnvOk`, so it adds no assumption beyond the
  caller contract ([trust](DESIGN.md)). So a receiver
  whose checked claim is proto-free is no instance, also of any other class,
  which the rule refuses alike. Being proto-free discriminates instances in
  this representation; it says nothing of a plain object's own
  non-enumerable properties, which the caller contract excludes.
- **What stays the parser's.** A field of an allocation is no write: an
  instance member, a parameter property, and a constructor's `this.k = e`,
  which the lowering makes a field of the instance's allocation, are
  reserved by the parser in a class extending `Error`. The parser's scan of
  the constructor follows arrows, which keep its `this`, and stops at a
  function, a method, an accessor or a class, which bind their own: their
  writes are writes, the rule's (`invalid-error-subclass-nested-function-write`). Lean reads no class
  declaration, and accepts a fragment, claims and evidence with a member
  renamed `stack` throughout (`pipeline/test.mts`, "forged stack member").
  Each write form of `reserved-write-twin`, its key renamed `stack` in the
  three documents, is a valid document only the rule refuses, located at the
  write, in search and in check ("forged reserved writes").

External code reaching an instance of the family is required to keep the
message contract the model represents and to create no enumerable own
`message` or `stack` on it. The message contract: `e.message` is a string,
the one the model's link holds; where the model re-reads the instance after
the external code runs (a call whose footprint may change it), any string
its declared type allows. This holds through a parameter type looser than
the instance's own, such as `{ message?: unknown }`: such code may not write
another value. The enumerability requirement excludes an assignment of
`message` to an instance constructed without a message and a definition of
either key as enumerable. A footprint states which locations a call may
change, not what a changed message holds or whether a key it creates is
enumerable, so neither requirement follows from an external function's
effect; both are stated of external code. With them, the admitted
observations after the call agree with the model: `e.message` reads a string
the model's type allows, and keys, copies and entries see the declared
fields alone; `e.stack` is refused.

The pipeline cases `error-subclass` and `error-subclass-methods` (run under
Node) and `invalid-error-subclass-*` hold each row, and forged claims of a
constructed instance owning `message` or holding `stack` are refused in
search and check (`pipeline/test.mts`).

### Class members

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

## Object spreads

A spread in an object literal copies its source's own enumerable
properties ([object literals](SOURCE-MODEL.md#object-literals)). The claims
a copy needs come from the two forms below: the literals whose own-key
bound a copy keeps, and the arms of an intersection it copies.

### Literals a spread copies

A copy replaces every key its source may own. A source of an open record
type may own any key, at any type, so a field written before its spread
is not the copy's: `{ name, ...s }` with $`s:\{\}`$ states no `name`
(`invalid-object-spread-union-open`). A fresh literal owns exactly the
keys it writes, and its claim states it with the own-key bound
$`\mathsf{among}\ \vec k`$. Two forms carry that bound from the literal to
a spread's source:

```math
\frac{f\ \text{a closure without a result annotation}\quad
      e\in\mathrm{returned}(f)\quad e=\{k_1{:}e_1,\ldots,k_n{:}e_n\}\quad \Gamma\vdash e_i:T_i}
     {\Gamma\vdash e:\mathsf{Ref}(k_1{:}T_1,\ldots,k_n{:}T_n;\ \varnothing;\ \mathsf{among}\ \{k_1,\ldots,k_n\})}\ \textsf{returned-literal}
```

where $`\mathrm{returned}(f)`$ is $`f`$'s expression body, or the operand of
each `return` of its block body outside nested closures, an async
closure's the payload each resolves its promise with, each read through
the arms of `?:`, the right operands of `&&`, `||`, `??` and `,`, and the
operands of a non-null assertion and of `satisfies`; and a constant without
an annotation whose object a later spread or `Object.assign` copies has its
initializer's literals, through the same positions, claimed with their
bounds. A literal expected at a writable dictionary is allocated at the
dictionary instead, since code holding it may add keys, which no own-key
bound admits. The closure's result is the union of
its returned claims, widened as TypeScript widens an inferred result, so a
spread of its call meets each literal's bound. A source clause bounded by
$`\mathsf{among}\ \vec k`$ gives nothing under a key outside $`\vec k`$, so the
merge keeps a field written before it there (`FieldsOk`,
[allocation from parts](PROGRAM-TYPING.md#allocation-from-parts)). This is
the bound TypeScript's inferred union of literals relies on, which states a
key one literal lacks as optional at `undefined`:
`p ? { rest: true as const } : {}` is
`{ rest: true } | { rest?: undefined }`, and the bound is what puts a value
of the second arm within it. A const assertion's type is not fresh: a field
`k: e as const` keeps $`e`$'s literal type. The claims are proposals: Lean
checks the bound at the allocation, and a written result, a returned name,
a call or any other source keeps its declared type, open where it is open
(`invalid-object-spread-annotated-result`,
`invalid-object-spread-returned-dictionary`;
`object-spread-exact-literals` verifies, each negative run under Node).

### A spread of an intersection

A value of $`A_1 \mathbin{\&} \cdots \mathbin{\&} A_n`$ is of every operand,
so it is of $`a_1 \sqcap \cdots \sqcap a_n`$ for some arm $`a_i`$ of each
$`A_i`$, and its copy is the copy of that meet. The arms of a type are its
union's members, a declaration's through its equation, and an
intersection's the meets of one arm of each operand, so a union operand
distributes:

```math
\mathrm{arms}(A \mathbin{\&} B)=\{\,a\sqcap b \mid a\in\mathrm{arms}(A),\ b\in\mathrm{arms}(B),\ a\sqcap b\neq\varnothing\,\}
```

Each meet $`a\sqcap b`$ has one of three outcomes: empty ($`\varnothing`$),
a record or primitive the copy reads, or refused. An empty meet contributes
no arm; a refused meet refuses the whole spread, whatever the other meets
of the union are; and the spread is refused where no arm remains.

For each product, the producer gathers every record operand before choosing
fields. For a key $`k`$, let $`I_k`$ index the operands stating it, with read
type $`T_i`$ and optionality $`o_i`$ ($`1`$ means optional). If any operand
states $`k`$ as a method, $`k`$ is a method of the arm, the copy does not
state it, and no field is selected for it. Otherwise a candidate must itself
supply the required presence. The proposal selects an existing field
$`j\in I_k`$ satisfying

```math
\forall i\in I_k,\ H(T_j,T_i)
\qquad\text{and}\qquad
\bigl(\forall i\in I_k,\ o_i=1\bigr)\ \lor\ o_j=0.
```

Its proposed field is $`k{:}T_j`$, optional exactly when every $`o_i=1`$.
Here $`H`$ is the producer's `plausible_subtype`
([`type_queries.ml`](../ocaml-producer/type_queries.ml)), a proposal
heuristic for inclusion: equality, literals within their primitive, members
of unions, and shapes with equal fields; it compares named types as written,
without expanding their declarations. Lean decides inclusion.

Thus `{ k: string | number } & { k: string | boolean } & { k: string }`
selects the third field, independently of operand order. An optional field
cannot supply a required key merely because its read type passes the test.

Products with incompatible primitive atoms, or both a primitive and a
record, contribute no arm, as Lean's clause meet drops them. Emptiness is
decided over the enclosing union: an empty intersection arm contributes
nothing, and the whole spread source is refused only when no alternatives
remain. A product with an unsupported field selection is refused even when
another product succeeds: `({ k: "a" } | { k: "b" }) & { k: "a" }` has such
a product. The heuristic does not decide that contradictory field
constraints make a record empty.

The copy of each surviving arm states its own enumerable string-keyed
fields, optional ones optional. The copy's type is the producer's proposal.
Lean checks the merge against the clauses it normalizes the operand's claim
to, where several fields of a key are constraints on its value
([allocation from parts](PROGRAM-TYPING.md#allocation-from-parts)), and
refuses a copy's field that no field of the source gives
(`spread-intersection-meet` and its forged-claim control in
`pipeline/test.mts`).

Refused at the spread's operand: a data key with no candidate recognized by
$`H`$ at the required presence (`{ k: "a" } & { k: "b" }`,
`{ k: string } & { k?: "a" }`); two operands with index signatures; a
callable met with a record with readonly or optional fields, methods or an
index; an intersection operand that is an array, a
type parameter, a cyclic declaration, or another unsupported shape; and a
source with no surviving alternative. A callable is met with a record only where the
record's fields are required writable data fields, whether the intersection
is written in an annotation or reached through a declaration. Every callable
operand in a product contributes all its signatures to one overloaded
callable, so the producer's proposal is the same whether they are written
flat or grouped through an alias; Lean's clause meet keeps both signature
lists of two callables. Lean reads an alias of function types met with a
record as an empty intersection (`spread-intersection-callable-alias`), so
the verifier refuses that grouping.

Within an intersection product, `Top` (`unknown`) is the identity; a source
consisting only of `Top` has no supported copy. `Exact` records are supported
as standalone spread sources, but an `Exact` operand inside an intersection
is outside this product algorithm, including when the other operand is
`Top`. Exact own-key bounds require a separate meet operation.

## Statement forms

The statement forms of a body are lowered to the graph compiler's where the
lowering is exact ([as graphs](PROGRAM-TYPING.md#statement-forms-as-graphs)). $`\Gamma\vdash_R S`$
reads "the statements $`S`$ are safe under $`\Gamma`$ in a function whose result
is $`R`$". An unbraced arm is the block holding it and `else if (c) S` is
`else { if (c) S }`; `return;` is `return undefined`, and a block closure that
does not return on every terminal arm ends with `return undefined`:

```math
\frac{\mathsf{undefined}\le R}{\Gamma\vdash_R\ \mathsf{return};}\ \textsf{return-bare}
\qquad
\frac{\Gamma\vdash_R S_1\quad S_1\ \text{always jumps}\quad \mathit{names}(S_2)\ \text{free in no live statement, none hoisted}}
     {\Gamma\vdash_R S_1;S_2}\ \textsf{dead}
```

`for (init; cond; update) S` is `{ init; loop }` with a `while (cond)` whose
body's end and every `continue` run `update`, then go to the head (a closure
capturing a `for` loop's `let` is refused, since JavaScript copies it per
iteration):

```math
\frac{\Gamma\vdash_R \mathit{init}:\Gamma'\quad \Gamma_h\ \text{the head's entry claims}\quad
      \Gamma'\le\Gamma_h\quad \Gamma_h\vdash c:\mathsf{boolean}\quad
      \Gamma_h\wedge c\vdash_R S\ \text{with}\ \mathsf{continue}\mapsto u\quad
      \Gamma_u\vdash \mathit{update}\ \text{back to}\ \Gamma_h}
     {\Gamma\vdash_R\ \mathsf{for}\ (\mathit{init};c;\mathit{update})\ S}\ \textsf{for}
```

`switch (d) { … }` is a labeled block per clause, nested in source order
inside one for the whole switch: the innermost holds the dispatch, each case
label in order `if (d === l) break` to the end of its clause's block, and
each clause's statements follow its block's end, so fall-through is ordinary
sequencing. The discriminant is evaluated once into a slot no source names,
unless it is a name or a field of a name and every label a literal or a name,
when it is re-read at each test. A name declared in one clause and read in
another is refused.

```math
\frac{\Gamma\vdash_R S\ \text{with}\ \mathsf{break}\ \ell\mapsto\Gamma_{\mathit{after}}\quad
      \Gamma_{\mathit{after}}\vdash_R S'}
     {\Gamma\vdash_R\ \ell:\{S\};S'}\ \textsf{labeled-block}
```

`for (const k in o) S` is `for (const k of %ForIn%(o)) S` with the trusted

```math
\mathtt{\%ForIn\%}:(o:\mathsf{unknown})\Rightarrow\mathsf{readonly}\ \mathsf{string}[\,],
```

the keys the loop visits: strings, for any value. Where the body reads the
entry at the key, `P[k]` with `P` the loop's operand spelled again (a name,
or a chain of named reads from one), before anything that could change the
entry runs, the loop steps the entries instead,
`for (const e of %Iterate:ForIn%(P)) { const k = e[0]; S' }` with each such
read in $`S'`$ the step's value `e[1]`:

```math
\mathtt{\%Iterate{:}ForIn\%}:\forall V.\ (o:\{\mathsf{readonly}\ [k:\mathsf{string}]:V\})\Rightarrow
  ()\Rightarrow\{\mathsf{readonly}\ \mathsf{value}:[\mathsf{string},V]\}\mid\mathsf{null},
```

each step a fresh array of a key the loop visits and the value the object
holds under it at the step. A dictionary holds no prototype, and a plain
object's, `Object.prototype`, no enumerable key, so every key visited is the
object's own, whose value the index's contract states. The reads rewritten
are those of the statements the body starts with that run no code and write
no property, outside the functions they define, and the whole initializer of
the declaration after them; the operand's name is written nowhere in the
outermost function holding the loop (the file, at the top level), and a
chain of reads is read from a body that runs no code and writes no
property, so each read finds the object the loop enumerates and the value
the step read (`forInEntryReads` in `tools/fragment-support.mts`). A read
after a call is the dictionary's read, `V | undefined`: the call may have
removed the key. `try B catch (e) C finally
F` names $`C`$'s entry as the handler of $`B`$'s nodes that may throw, with `e`
at `unknown` (the only annotation admitted), and compiles $`F`$ on every way
out: after a normal completion, before each `return` with the value held,
before each `break` or `continue` leaving it, then on to the jump's target
through the `finally` of every enclosing `try` the jump also leaves, after a
throw with the thrown value held and rethrown. A `return`, `throw`, `break`
or `continue` in $`F`$ leaves by its own way, as JavaScript's replaces the
pending completion:

```math
\frac{\Gamma\vdash_R B\ \text{with throws}\mapsto(\mathsf{unknown},\Gamma)\vdash_R C\quad
      \Gamma\vdash_R F\ \text{on each way out}}
     {\Gamma\vdash_R\ \mathsf{try}\ B\ \mathsf{catch}\ (e)\ C\ \mathsf{finally}\ F}\ \textsf{try}
```

The handler's and finalizer's entries state each cell at its contract, since
a throw may leave after any part of the body ran.

## Guards

Every guard is a tag test ([SEMANTICS](SEMANTICS.md#operational-language)),
refining a tested immutable binding by the tag slice $`T_q`$ of its type on
each edge ([refinement](PROGRAM-TYPING.md#refinement-under-an-observed-outcome)).
A call of a [user-defined guard](#user-defined-guards) narrows by such tests
of its argument, run again after the call:

```math
\frac{\Gamma(x)=A\quad\Gamma[x:T_{\mathsf{typeofObject}}(A)]\vdash_R S_1\quad\Gamma[x:T_{\lnot\mathsf{typeofObject}}(A)]\vdash_R S_2}
     {\Gamma\vdash_R\ \mathsf{if}\ (\texttt{typeof}\ x\equiv\texttt{"object"})\ S_1\ \mathsf{else}\ S_2}\ \textsf{if-typeof-object}
```

```math
\frac{\Gamma(x)=A\quad A\ \text{objects, no class value}\quad \kappa\notin\mathcal B\quad
      \Gamma[x:T_{\mathsf{hasKey}(\kappa)}(A)]\vdash_R S_1\quad\Gamma[x:T_{\lnot\mathsf{hasKey}(\kappa)}(A)]\vdash_R S_2}
     {\Gamma\vdash_R\ \mathsf{if}\ (\texttt{"}\kappa\texttt{"}\ \mathtt{in}\ x)\ S_1\ \mathsf{else}\ S_2}\ \textsf{if-in}
```

with $`\mathcal B`$ the refused keys (`inKeyRefusal`: `Object.prototype`'s,
`Array.prototype`'s and `Function.prototype`'s own string keys, array
indices, and the keys the model reserves). `in`'s answers are by keys the
types state (`inAnswer`): a failed test drops an arm owning the key, a passed
one drops an arm whose key bounds exclude it and the prototype key, and every
primitive; a passed test promotes an optional key to a field (`promote`). A
test against a claimed singleton $`c`$ of any primitive kind, and against a
field of an immutable binding's object, narrows the binding or the object's
arms:

```math
\frac{\Gamma\vdash a:A\quad \Gamma\vdash k:\{c\}\quad
      \Gamma[x:T_{\mathsf{eq}(c)}(\Gamma(x))]\vdash_R S_1\quad
      \Gamma[x:T_{\lnot\mathsf{eq}(c)}(\Gamma(x))]\vdash_R S_2}
     {\Gamma\vdash_R\ \mathsf{if}\ (x\equiv k)\ S_1\ \mathsf{else}\ S_2}\ \textsf{if-singleton}
\qquad
\frac{\Gamma\vdash k:\{c\}\quad
      \Gamma[o:F^{f}_{\mathsf{eq}(c)}(\Gamma(o))]\vdash_R S_1\quad
      \Gamma[o:F^{f}_{\lnot\mathsf{eq}(c)}(\Gamma(o))]\vdash_R S_2}
     {\Gamma\vdash_R\ \mathsf{if}\ (o.f\equiv k)\ S_1\ \mathsf{else}\ S_2}\ \textsf{if-field}
```

with $`F^f`$ the field slice. The truthiness of a field of an immutable
binding's object, where an arm of it leaves the field optional or unnamed (so
that no fact about what the field holds is claimed, as of an
`IteratorResult`'s `done`), narrows the object's arms the same way, the read
dispatched on its truthiness:

```math
\frac{\Gamma[o:F^{f}_{\mathsf{truthy}}(\Gamma(o))]\vdash_R S_1\quad
      \Gamma[o:F^{f}_{\lnot\mathsf{truthy}}(\Gamma(o))]\vdash_R S_2}
     {\Gamma\vdash_R\ \mathsf{if}\ (o.f)\ S_1\ \mathsf{else}\ S_2}\ \textsf{if-field-truthy}
```

Where the singleton $`c`$ is a string or a number other than a zero, a passed
test leaves the operand $`c`$ alone, whatever its type was, `unknown`
included: $`T_{\mathsf{eq}(c)}(A)=\{c\}`$ for every $`A`$ the test may pass
on (`tagMember`). A disjunction's passed outcome came from either operand,
and each slot holds what either path left it, a slot one path leaves at its
input type keeping that type:

```math
\frac{\Gamma_1=\Gamma[a\mapsto\mathsf{true}]\quad
      \Gamma_2=\Gamma[a\mapsto\mathsf{false}][b\mapsto\mathsf{true}]\quad
      \Gamma_1\sqcup_\Gamma\Gamma_2\vdash_R S_1\quad
      \Gamma[a\mapsto\mathsf{false}][b\mapsto\mathsf{false}]\vdash_R S_2}
     {\Gamma\vdash_R\ \mathsf{if}\ (a\parallel b)\ S_1\ \mathsf{else}\ S_2}\ \textsf{if-or}
\qquad
(\Gamma_1\sqcup_\Gamma\Gamma_2)(x)=\begin{cases}\Gamma(x)&\Gamma_1(x)=\Gamma(x)\lor\Gamma_2(x)=\Gamma(x)\\
  \Gamma_1(x)\cup\Gamma_2(x)&\text{otherwise}\end{cases}
```

with $`\Gamma[a\mapsto q]`$ the refinement by $`a`$'s answer $`q`$, and `&&`'s
false outcome the same join. Each edge into $`S_1`$ is checked against the
joined context, so `v === "dense" || v === "sparse"` leaves `v` at
`"dense" | "sparse"` (`literal-union-narrowing`). An operand testing a field
of an immutable binding's object refines that object by its field slice
$`F^f`$, as `if-field` does, so `n.kind === 1 || n.kind === 2` leaves `n` at
the arms whose `kind` admits 1 or 2 (`field-test-disjunction`).

`x === y` with `x` claimed at a union of
singletons is dispatched as the disjunction over its singletons $`c`$ of
$`x\equiv c\land y\equiv c`$ (`savedSplit` where `x` has effects). Strict
equality without a singleton is the $`\equiv`$ operator of `arith`, which
narrows nothing and is refused between two operands that may both be objects
without a field. `x instanceof C`, for a class the file declares at its top
level, is $`\mathsf{hasKey}(\kappa_C)`$ ([derived form](SOURCE-ELABORATION.md#derived-source-forms)).
It does not narrow `unknown`: an object gets $`C`$'s prototype without $`C`$'s
constructor running (`Object.create(C.prototype)`), so the key is no evidence
of $`C`$'s fields. `Array.isArray(x)` narrows a record or dictionary arm of $`x`$
to the built-in `sparse ReadonlyArray<unknown>` where it holds
([**tag-array**](PROGRAM-TYPING.md#refinement-under-an-observed-outcome)), and keeps
`unknown`, which the array invariant says nothing of:

```math
\frac{\Gamma(x)=A\quad A\preceq_{\mathsf{isArray}=\mathsf{true}}B\quad \Gamma[x:B]\vdash_R S_1\quad
      \Gamma[x:T_{\lnot\mathsf{isArray}}(A)]\vdash_R S_2}
     {\Gamma\vdash_R\ \mathsf{if}\ (\mathtt{Array.isArray}(x))\ S_1\ \mathsf{else}\ S_2}\ \textsf{if-array}
```

### User-defined guards

A type guard `function g(x: A): x is T` and an assertion function
`function f(x: A): asserts x is T` have function types of two signatures each,
the plain one and a **promise signature** about the parameter $`x`$, the
$`p`$-th:

```math
g : (A) \to \mathtt{boolean}\ \land\ (A) \to T\,[\mathsf{guards}\ p]
\qquad
f : (A) \to \mathtt{void}\ \land\ (A) \to T\,[\mathsf{asserts}\ p]
```

A promise signature's result operand is the promise's type. Its meaning is the
[effect-qualified call contract](SEMANTICS.md#effect-qualified-call-contracts)
whose result family relates the result $`v`$ to the $`p`$-th actual $`v_p`$:
a call of $`g`$ returns `true` with $`v_p \in T`$, or `false`; a normal return
of $`f`$ is `undefined` with $`v_p \in T`$. The same declaration reads the
same in every position: a function type, a method, an imported module's
declaration and a closure's annotation all carry both signatures.

The promise is proved at the definition. The body is checked at the promise
signature with the goal that each return meets the result family for the
argument $`v`$ the call passed. The checker tracks the slots holding $`v`$,
which a write of the parameter or a default replacing it leaves, and at each
return asks for the answer and the argument's type where that answer is
possible:

```math
\frac{\begin{array}{c}\Gamma_0 = x{:}A \qquad
      \forall\ \mathsf{return}\ e \text{ at } \Gamma \text{ with } x \text{ holding } v:\
      \Gamma\vdash e : \mathtt{boolean} \quad
      \bigl(\Gamma\vdash e : \mathtt{false}\ \lor\ \Gamma_{e=\mathtt{true}} \vdash v : T\bigr)\end{array}}
     {\vdash g : (A) \to T\,[\mathsf{guards}\ p]}\ \textsf{guard-def}
```

```math
\frac{\forall\ \text{normal completion at } \Gamma \text{ with } x \text{ holding } v:\
      \Gamma\vdash v : T}
     {\vdash f : (A) \to T\,[\mathsf{asserts}\ p]}\ \textsf{assert-def}
```

$`\Gamma_{e=\mathtt{true}}`$ is $`\Gamma`$ refined by what the returned value
being `true` establishes: a test of a slot (`typeof x === "string"`, a strict
equality, a conjunction or disjunction of these), a Boolean slot carrying such
a test's answer, or a call at a promise signature. A test of a value read
from a field refines the object it was read from, while the read is current,
to the arms whose field answers the test so (`return s.kind === "circle"`).
A branch before the return refines $`\Gamma`$ itself. A return
is claimed at its value's own type, so a `return false` answers `false`
alone.

A call consumes the promise. The callee is any expression whose type holds
a promise signature its actuals meet: a name, a method or a field of an
object, a bound function. Of an overloaded callee's promise signatures, the
call narrows by one whose parameters admit its actuals. The call's `true`
result, or its normal return, leaves the promised actual $`a`$, a name, a
$`T`$:

```math
\frac{\Gamma\vdash g : (\vec A)\to T\,[\mathsf{guards}\ p]\quad \Gamma\vdash \vec a : \vec A\quad
      \Gamma[a_p : T]\vdash_R S_1\quad \Gamma\vdash_R S_2}
     {\Gamma\vdash_R\ \mathsf{if}\ (g(\vec a))\ S_1\ \mathsf{else}\ S_2}\ \textsf{if-guard}
\qquad
\frac{\Gamma\vdash f : (\vec A)\to T\,[\mathsf{asserts}\ p]\quad \Gamma\vdash \vec a : \vec A\quad
      \Gamma[a_p : T]\vdash_R S}
     {\Gamma\vdash_R\ f(\vec a);\ S}\ \textsf{assert-call}
```

A conditional expression narrows its first arm the same way, a closure the
arm creates reading the actual at $`T`$ (`guard-ternary-closure`):

```math
\frac{\Gamma\vdash g : (\vec A)\to T\,[\mathsf{guards}\ p]\quad \Gamma\vdash \vec a : \vec A\quad
      \Gamma[a_p : T]\vdash e_1 : B\quad \Gamma\vdash e_2 : B}
     {\Gamma\vdash g(\vec a)\ ?\ e_1 : e_2 : B}\ \textsf{cond-guard}
```

A `false` outcome narrows nothing: the promise states nothing of it
(`invalid-type-guard-false-branch`). Passing a guard where a plain predicate
is expected forgets its promise signature, as an intersection's operand.
Binding a prefix of a guard's actuals (`g.bind(r, …)`) keeps a promise about
an actual past the prefix, at its new position.

A closure's written promise is proved whatever its claim offers: one of the
signatures its code is checked at states that promise over the annotation's
whole domain, admitting every receiver and argument the annotation admits,
at a type within the written one, or the closure is refused. A guard
closure passed where a callback binding more parameters is expected
(`every`'s or `filter`'s predicate) is claimed at its own signature, its
promise and the longer signature, its body checked at each
(`guard-closure-callback`). Where the longer signature states the
closure's written promise (`filter`'s guard overload,
[`native-guard-filter`](SOURCE-CONTRACTS.md#prototype-contracts)), the closure is claimed at it
with that promise, and its body is checked at it with the promise goal. The
reviewed `every` states no guard overload (`every<S>`), so a call passing a
guard does not narrow its receiver.

An imported guard is read at its declared type, both signatures; its promise
is the import assumption of [the trust surface](DESIGN.md#trust-surface),
discharged where the imported module's own run verifies the guard. A guard
of a host family is read instead from its audited table entry
([guard recognition](HOST-FAMILIES.md#guard-recognition)), never at its
declared predicate; the entry rests on the host assumption that the
package's enum objects and its guards' bindings are never written, by the
program or by external code, and a source write to them is refused.

Implementation: `CallEffects.Effect` (`guards p`, `asserts p`) gives the
contract; `ControlFlow.Goal` states a body's goal and `checkReturnResult` its
check at a return; [PromiseCalls.lean](../lean/Verification/Programs/PromiseCalls.lean)
holds the yields of a returned value (`yieldFollows_sound`) and the promise
call (`promiseCall_sound`); `Lowering.Control.promiseNarrowing` places the
narrowed claim after a call, which the edge check verifies. Pipeline cases:
`type-guards`, `type-guard-objects`, `type-guard-methods`,
`type-guard-value-import` and `type-guard-overload-value-import` verify;
`invalid-type-guard-promise`, `invalid-type-guard-undefined`,
`invalid-type-guard-default`, `invalid-type-guard-object`,
`invalid-type-guard-field-test`,
`invalid-type-guard-method` and
`invalid-assertion-promise` are refused at the return where the argument is
not a $`T`$, each run under Node by `node-runs.mts`.

## Loops and spreads over iterables

`for (const x of e) S` steps a trusted **iteration intrinsic**, one per kind
of host iterable, which the parser picks by TypeScript's type of $`e`$
(`iterationKind` in `declaration-graph.mts`, every part of a union alike).
With $`\mathit{Step}(E)=()\Rightarrow\{\mathsf{readonly}\ \mathit{value}:E\}\mid\mathsf{null}`$:

```math
\begin{array}{ll}
\mathtt{\%Iterate\%}:\forall T.\ (\mathsf{readonly}\ T[\,])\Rightarrow\mathit{Step}(T) & \text{an array or tuple}\\
\mathtt{\%Iterate{:}string\%}:(\mathsf{string})\Rightarrow\mathit{Step}(\mathsf{string}) & \text{a string, by code point}\\
\mathtt{\%Iterate{:}Set\%}:\forall T.\ (\mathsf{Set}\langle T\rangle)\Rightarrow\mathit{Step}(T) & \\
\mathtt{\%Iterate{:}Map\%}:\forall K\,V.\ (\mathsf{Map}\langle K,V\rangle)\Rightarrow\mathit{Step}([K,V]) & \text{a fresh entry per step}\\
\mathtt{\%Iterate{:}Iterator\%}:\forall T.\ (\mathsf{NativeCollectionIterator}\langle T\rangle)\Rightarrow\mathit{Step}(T) & \text{a SetIterator or MapIterator}
\end{array}
```

`Set` and `Map` are the [interface overlay](SOURCE-CONTRACTS.md#library-types)'s, whose
`keys`, `values`, `entries` and `[Symbol.iterator]` give a `SetIterator` or
`MapIterator` read as the native collection iterator
$`\mathsf{NativeCollectionIterator}\langle T\rangle`$: `Iterator<T>` with
a key $`\langle\mathit{CollectionIterator}\rangle`$ at `undefined`, a
synthetic symbol no source declaration, literal or class states, so no
other value meets it. A value TypeScript types `SetIterator` or
`MapIterator` from any other source, a `ReadonlySet`'s or `ReadonlyMap`'s
iterator included, is no argument of `%Iterate:Iterator%`, and its loop is
refused (`invalid-readonly-set-iterator-native`, run under Node). None of these iterators has a `return`, so a
loop left early by `break`, `return` or a throw calls nothing. An iterable of
any other kind with a `[Symbol.iterator]` (an `Iterable<T>`, a class or a
record with one), or a union with one, is the program's, and runs the
[iterator protocol](#the-iterator-protocol); any other steps `%Iterate%`,
whose typing then refuses what is no array. Lean compiles the loop over a
host iterable itself (`SourceExtraction.body`), $`\mathit{it}`$ the picked
intrinsic:

```math
⟦\mathsf{for}\ (\mathsf{const}\ x\ \mathsf{of}\ e)\ S⟧=
n\leftarrow\mathit{it}(⟦e⟧);\
\mathit{head}:\ r\leftarrow n();\
\mathsf{if}\ r\ \mathsf{is\ null}\ \mathsf{then}\ \mathit{exit}\
\mathsf{else}\ x\leftarrow r.\mathit{value};\ ⟦S⟧;\ \mathsf{goto}\ \mathit{head}
```

`n` is a slot at the call's claimed type, the head a cut stated by the loop's
entry claims, `continue` and the body's end go to the head and `break` to the
exit; the tag dispatch refines `r` on each arm (`tagBind isNul`). The derived
rule, with $`\mathit{it}:\forall\vec\alpha.\ (P)\Rightarrow\mathit{Step}(E)`$ and
$`\sigma`$ the call's instance:

```math
\frac{\Gamma\vdash e:A\quad A\le P\sigma\quad
      \Gamma_{\mathit{head}},x:E\sigma\vdash S\quad \Gamma_{\mathit{head}}\ \text{the loop's entry claims}}
     {\Gamma\vdash\mathsf{for}\ (\mathsf{const}\ x\ \mathsf{of}\ e)\ S}\ \textsf{for-of}
```

The native iterator requires a readable array receiver, so every in-bounds
read yields `T`, including a hole when `T` admits `undefined`. A sparse store
needs a separate proof of readability before it satisfies that contract. Array patterns read positions under the same trust
([patterns](SOURCE-ELABORATION.md#patterns)).

An argument spread `f(…, ...e, …)` over an iterable of one of the other kinds
is the spread of the fresh array its iterator yields, collected where the
spread is written: $`\ldots e\equiv\ldots\mathtt{\%Spread{:}K\%}(e)`$, with
$`\mathtt{\%Spread{:}K\%}:\forall\vec\alpha.\ (P)\Rightarrow E[\,]`$ for each
$`\mathtt{\%Iterate{:}K\%}:\forall\vec\alpha.\ (P)\Rightarrow\mathit{Step}(E)`$, the
array of what that step yields until $`\mathsf{null}`$. It is an ordinary call
of a trusted value, and the array an ordinary spread into a variadic
callee. A spread of a program's iterable is collected by the
[protocol](#the-iterator-protocol).

A tuple meets `Iterable<T>` through the readonly array of its positions: the
producer claims a tuple expected at an iterable other than an array at
$`\mathsf{readonly}\ (A_0\cup\ldots\cup A_{n-1})[\,]`$, which Lean derives from
the tuple ($`\mathsf{list}`$ inclusion) and relates to the iterable through
`Array.prototype[Symbol.iterator]`, as for any array. A compiler-API node
list is read as a dense readonly array of its elements
([node lists in the model](COMPILER-API.md#node-lists-in-the-model)): its own
`Symbol.iterator` yields what indexing reads, which T4 states and C4 runs, so
it is iterated as that array in every position, under the host assumption on
the package's values (`compiler-api-node-list-spread`).

## The iterator protocol

An iterable the program defines is iterated as
[ECMA-262](REFERENCES.md#ecma-262)'s ForIn/OfBodyEvaluation runs it, in
ordinary forms the parser writes (`protocolForOf`), each an ordinary call or
read typed by the declarations TypeScript gives the iterable (`Iterable<T>`,
`Iterator<T, TReturn, TNext>`, `IteratorResult<T, TReturn>`, or the program's
own class or record), under names no source spells:

```math
\begin{array}{l}
[\![\mathsf{for}\ (\mathsf{const}\ x\ \mathsf{of}\ e)\ S]\!]=
\{\ \mathsf{const}\ i=e[@@\mathit{iterator}](),\ n=i.\mathit{next}.\mathsf{bind}(i);\\
\quad\mathsf{while}\ (\mathsf{true})\ \{\ \mathsf{const}\ r=n();\ \mathsf{if}\ (r.\mathit{done})\ \mathsf{break};\
  \mathsf{const}\ x=r.\mathit{value};\ \mathsf{closing}\ \{S\}\ \mathsf{close}\ C_i\ \}\ \}\\[2pt]
C_i=\mathsf{const}\ m=i.\mathit{return};\ \mathsf{if}\ (\mathsf{typeof}\ m\ne\texttt{"undefined"})\ \{\ \mathsf{const}\ \_:\mathsf{object}=m.\mathsf{call}(i)\ \}
\end{array}
```

The protocol lowering writes `.bind` in the fragment to save a method with
its receiver. Source-written `.bind` is admitted by the parser only on a
known local function.

GetIterator reads `next` once, and each step calls it on the iterator: the
bound function is that call ([`bindMember`](PROGRAM-TYPING.md#judgments-and-constructor-views)). A
`return` the iterator's type declares a required method is read bound the
same way, $`C_i=\mathsf{const}\ m=i.\mathit{return}.\mathsf{bind}(i);\ \mathsf{const}\ \_:\mathsf{object}=m()`$;
an optional one or a property is read, tested and called on the iterator, as
GetMethod and IteratorClose do. The result must be an object, which is the
TypeError IteratorClose throws otherwise, made impossible by the annotation's
obligation. The test of `r.done` refines $`r`$ to the arms whose `done` may be
falsy (a [field slice](PROGRAM-TYPING.md#refinement-under-an-observed-outcome) through the
read's link, optional where `IteratorYieldResult` leaves `done` optional), so
`r.value` is read at the not-done arm's type, `T`. An iterator whose type
states no `return` is refused where the loop could close it: an open record
may own any `return`. An array's `values`, `keys` and `entries` give the
`ArrayIterator` the library declares, read at the overlay as
`IterableIterator` of the declared argument (`[number, T]` for `entries`):
the iterator is its own, and a program's iterable by this rule, its `return`
read `undefined` and the close calling nothing, by the
[host assumption](DESIGN.md#trust-surface) that its chain holds none.

GetIterator on an iterable of a union type gives a union of iterators, and
the protocol binds the `next` (and a required `return`) of whichever iterator
it is: a [member bound to a union of hosts](PROGRAM-TYPING.md#judgments-and-constructor-views),
each host's member taken at the signature it binds alone. Each step's result
is then the union of the hosts' results, `IteratorResult<T_j, TReturn_j>`
each, and `r.value` past the test of `r.done` the union of the not-done arms'
`T_j`. The `next` the protocol admits, per host, is a method member whose
signature takes no required parameter (`next()`, or the rest-tuple union
`next(...[value]: [] | [TNext])`, whose first signature is `next()`), with no
promise, under a receiver the iterator is within, returning a record with
`done` and `value`; the hosts' `next` signatures take the same parameters at
the same effect. Refused: a required parameter (the step's call passes none),
hosts' signatures that differ in parameters or effect, a result that is no
object (IteratorStepValue throws on it; the step's `done` read has no rule on
a primitive), a receiver the iterator is
not (`this: S`), an optional `next` or an accessor (outside the fragment), and
a `next` that is a field holding a function in a union, which no rule binds.
A `next` with effects changes what the loop's body and what follows know, as
any call of its footprint does.

The library's declarations are read by the rules of
[library types](SOURCE-CONTRACTS.md#library-types): `Iterable<T>` is the record of its one
method under the built-in `Symbol.iterator` key, returning an `Iterator`, and
so no `Iterator`, whose `next` it lacks; `Iterator`'s
`next(...[value]: [] | [TNext])` is the two signatures `next()` and
`next(value: TNext)` (**rest-tuples**), and its `return?` and `throw?` are
optional methods: optional fields whose functions take the iterator as
receiver ([records](POSITIVE-TYPES.md#records)), which is what the close's
test of `return` reads.

The closing region is a `finally` that runs on some ways out of $`S`$ only,
compiled by the machinery of `try` (`SourceExtraction.body`, `Finalizer`):

```math
\frac{\begin{array}{c}
\Gamma\vdash_R S\ \text{with}\ \mathsf{break}\mapsto C;\mathit{exit},\quad
  \mathsf{return}\ v\mapsto C;\mathsf{return}\ v,\quad
  \mathsf{continue}\mapsto\mathit{head},\quad
  \mathsf{throw}\ u\mapsto(\mathsf{try}\ C\ \mathsf{catch}\ \{\});\mathsf{throw}\ u\\
\Gamma\vdash_R C\ \text{on each of those ways}
\end{array}}
     {\Gamma\vdash_R\ \mathsf{closing}\ \{S\}\ \mathsf{close}\ C}\ \textsf{closing}
```

The close runs before a `break` of the loop leaves it, before a `return`
returns the value held in a slot of its own (as through any `finally`), and,
its own throws discarded by a handler that drops them, before a throw out of
the body is thrown again: IteratorClose with a throw completion keeps the
body's. Its end and a `continue` go to the head, and a done result leaves
without it, as IteratorClose is not called there. A jump past the loop to an
outer target passes it as it passes a `finally`. Every edge is checked as
any other; the close's statement entries state each cell at its contract.

A pattern $`p`$ binding the loop binds the step's value to a name no source
spells, where $`x`$ is bound, and destructures it as the closing region's
first statement:

```math
\mathsf{const}\ r=n();\ \mathsf{if}\ (r.\mathit{done})\ \mathsf{break};\
\mathsf{const}\ \%e=r.\mathit{value};\
\mathsf{closing}\ \{\ \mathsf{const}\ p=\%e;\ S\ \}\ \mathsf{close}\ C_i
```

ForIn/OfBodyEvaluation runs ForDeclarationBindingInitialization of $`p`$ on
the step's value after IteratorValue and before the body, and on its abrupt
completion returns IteratorClose with it: a throw of a default or of a read
the pattern makes closes the iterator, its own throw discarded, as a throw out
of $`S`$ does, and a default has no other way out. The pattern runs between two
steps of the protocol, so its code runs where JavaScript runs it. The inner
declaration is a `const` pattern's over a value another reference may hold
(the iterator may keep it), with every rule of
[patterns](SOURCE-ELABORATION.md#patterns): an array pattern reads the
positions of an array, with no code that may change it between its steps, its
nested patterns and defaults included
(`for-of-pattern-program-iterable-default-refused`); an array pattern over a
value that is no array (a string, a `Set`, an iterable the program defines)
is refused by the typing of those reads
(`for-of-pattern-nested-iterable-refused`), and a position past a short
array is `undefined` (`invalid-for-of-pattern-program-iterable`, run under
Node). It is the same lowering as a pattern over an array's loop
(`forOfPattern`), inside the region (`for-of-pattern-program-iterable`).

A spread of a program's iterable (`collect`) that is the first evaluation
able to run code of the statement's value (an expression statement's, a
`return`'s or a declaration's one initializer), every evaluation before it
a literal or a name the file never assigns whose read cannot throw nor run
code: a parameter, a function declaration with a body (an ambient
`declare function` is none, `spread-program-iterable-ambient-function-refused`),
a function body's `let` or
`const` the early-binding analysis finds initialized at every read, or a
name the file declares nowhere that TypeScript binds to the standard
library's `var`s or functions alone, whose read runs no code by the
[host assumption](DESIGN.md#trust-surface) on standard-library global
bindings. A module binding, an import, a class,
an ambient declaration or an unresolved name is none
(`spread-program-iterable-uninitialized-refused`,
`spread-program-iterable-global-getter-refused`,
`spread-program-iterable-global-tdz-refused`, each run under Node). Such a
spread is collected before the statement, where nothing the statement evaluates before the spread can be
changed by the iterator's code. Evaluation is followed in JavaScript's
order: an array literal's elements, a call's or a construction's callee then
arguments (a callee that is such a name, or a method read off a value whose
first evaluation is the spread), a member read's object. So the spread may
be the first element of an array literal before others, an argument of
`new Set(…)`, or the receiver of a method call (`spread-program-iterable-first`,
run under Node: the iterator's steps precede the later element's code): $`\mathsf{const}\ a=[\,],\ i,\ n;\ \mathsf{while}\ (\mathsf{true})\ \{\ \mathsf{const}\ r=n();\ \mathsf{if}\ (r.\mathit{done})\ \mathsf{break};\ a.\mathit{push}(r.\mathit{value})\ \}`$, then $`\ldots a`$ (or $`a`$ for the literal);
a spread steps to the end and closes nothing. An array literal's spread of
a host iterable (a string, a `Set`, a `Map`, a host collection iterator)
spreads its spread intrinsic's array, `[…, ...e, …]` $`\equiv`$
`[…, ...%Spread:K%(e), …]`, the fresh array of what the host's iterator
yields, as an argument spread of one is; the literal is a fresh array of its
own, at the store contract its claim states, also where the spread is its
one element (`array-literal-host-spread`). An array pattern
`const [p₀, …, ...q] = e` over one (`protocolPattern`) steps once per element,
a hole too, into cells $`v_j`$ starting `undefined`, leaves a labeled block when
a step is done, collects the rest to the end, and without a rest closes the
iterator after the elements, as IteratorBindingInitialization does; the
source's names are then bound from the cells, which binding names does not
observe. A default or a nested pattern, which run code between the steps, is
refused.

## Patterns

A pattern binds names from one value, in pattern order, and has no rule of its
own: it is reads, a tag dispatch and lets. Write
$`\Gamma\vdash p\Leftarrow(t{:}R)\dashv\Delta`$ when binding pattern $`p`$ to the
value term $`t`$ reads at $`R`$ under $`\Gamma`$ extends the scope by $`\Delta`$
(`bindPattern` in `BindingPlan.lean`). A name
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
iterator protocol's steps ([loops](#loops-and-spreads-over-iterables)).

A pattern binding a `for...of` binds each element, then reads it, before the
body, as JavaScript binds it per iteration:

```math
\mathtt{for}\ (\mathtt{const}\ p\ \mathtt{of}\ e)\ s\ \rightsquigarrow\ \mathtt{for}\ (\mathtt{const}\ \%e\ \mathtt{of}\ e)\ \{\ \mathtt{const}\ p = \%e;\ s\ \}
```

with $`\%e`$ a name no source spells and the inner declaration a `const`
pattern's (`for-of-pattern-binding`, `invalid-for-of-pattern-string`); over an
iterable the program defines, the inner declaration is the first statement
of the protocol's closing region
([iterator protocol](#the-iterator-protocol)).

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
activation or to a private cell ([slot or cell](#slot-or-cell)): a slot is
rebound at each write, and no call, closure run or throw changes it; a
closure holds a cell's identity. Its
contract $`C`$ is fixed where it is declared, the annotation or the
producer's proposal; the initializer and every write
are checked against it (`storage-contract`). A point claim for the name is
the slot's type there, checked on every incoming edge as any slot's is, or
describes the cell's current contents, which the
[current-content rules](PROGRAM-TYPING.md#current-content-rules-semantic-layer) justify on every
incoming edge.

### Slot or cell

A cell is how a binding is shared with the closures that
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

A closure's parameter is decided by the same rule over the closure's own
activation: for a parameter $`x`$ of $`\lambda\overline{y}.\,b`$,
$`\mathrm{writes}(x)`$ are its initialization, at the argument or, where the
argument is `undefined`, at its default's value, and the writes of $`x`$ in a
run of $`b`$, and $`\mathrm{creates}(x)`$ the
closures created in that run whose bodies mention $`x`$; the closure body's
`cells` list it where $`\neg\mathrm{slot}(x)`$. A test of a slot narrows it as
it narrows a constant, and the narrowing lasts until the next write, which
rebinds the slot at what it writes:

```math
\frac{\mathrm{slot}(x)\quad \Gamma(x)=T\quad
      \forall v\in T.\ \mathrm{test}(v)\Rightarrow v\in T_{+}\quad
      \forall v\in T.\ \neg\mathrm{test}(v)\Rightarrow v\in T_{-}}
     {\Gamma\vdash \mathrm{test}(x)\colon\ \Gamma[x\mapsto T_{+}]\ \text{on the true edge},\ \ \Gamma[x\mapsto T_{-}]\ \text{on the false edge}}
\qquad
\frac{\Gamma\vdash e\colon V\quad V\le C}{\Gamma\vdash x = e\colon\ \Gamma[x\mapsto V]}
```

A point claim for $`x`$ is checked on every incoming edge, a loop's back
edge included, so the refinement holds at a point only where every path into
it established it since the last write. A cell's point claim states only its
current-content predicates, primitive refinements and nullish exclusions, so
a test of the object a cell holds does not narrow it.

A condition's outcomes are proposed along its execution plan, in
evaluation order: each test refines the state where it runs, each later step
acts on that state, and the paths reaching one answer are joined. So a
field's contents a left operand of `&&` found are forgotten past a call in
its right operand, which may write any cell, while the arm the test selected
for an immutable binding, a lifetime fact, stays (`condition-effect-order`;
`invalid-condition-stale-call`, `invalid-condition-stale-branch`,
`invalid-condition-stale-disjunction`, run under Node).

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

### Constants

A `const` copy holds a snapshot. An unannotated constant of a named union is
held at the union's arms, as an annotated one is, and an annotated one
initialized by an object literal at the arms the literal may be of
(TypeScript's narrowing on assignment); a constant's object literal used whole
where an optional field it leaves out is expected is claimed with its exact
keys.

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

### Lexical bindings before initialization

A `let`, `const` or class
declaration's binding exists from the entry of its scope and is
uninitialized until its declaration runs; reading, writing or `typeof` of it
then throws a `ReferenceError` (the temporal dead zone). A closure holds the
binding, never its value, so whether a read through a closure throws depends
on when the closure runs, not on where it is written: in

```ts
const visit = (n: Node): void => { if (wanted(n)) found.push(n); };
const wanted = (n: Node): boolean => n.kind === 79;
```

`visit` reads `wanted` successfully at every call made after the second
line, and throws at a call made before it.

#### Scope

The model covers a `let` or `const` that declares one name (no
pattern), in a function body or a block statement, a loop's body included.
Each entry of the block creates its bindings anew, so a closure created in
one iteration keeps that iteration's. Refused at their location, as
explicit restrictions, each the behaviour of reading a binding of an
environment the model does not represent before its initialization: an
early binding (defined in this section) declared by a pattern; one in a `switch`'s case block
(one environment for every clause, entered after the discriminant, whose
clauses may skip a declaration); a class declaration's binding; a
generator's body; a parameter default that mentions its own parameter or a
later one, a closure's mention included (`initializedBefore`); and a loop
head's binding mentioned in its own head (`for (const xs of xs)`). A module's constants keep the initialization order check
(`Sites.checkInitializationOrder`), which refuses an initialization step
that may reach a constant not yet bound; it does not model the module's dead
zone for them, a caught `ReferenceError` there or a module cycle. A
module-level `let` is a [module cell](#module-cells).

A binding is **early** when one of its mentions is in a closure created
before its initialization point, which may run at any time after its
creation, or when a
mention in the scope's own code is not dominated, within the same
activation, by the binding's **initialization point**: the write after its
initializer completed normally, which follows the initializer's own
evaluation (`let x = x` and `let a = b, b = 1` throw), one binding of a
declaration list at a time. A function literal that is a constant's whole
initializer is the exception: creating it runs nothing, so its reads of the
constant are the [recursive constant](#recursive-constants)'s self entry,
not checked accesses. Every other binding is a slot or a cell ([slot or cell](#slot-or-cell)). A function
declaration in a body, which JavaScript creates when its block is entered
(`f(); let x = 1; function f() { return x; }` throws), is outside the
fragment (refused at the declaration); the parser's analysis takes its
creation at the block's entry.

#### Representation

An early binding $`x`$ of storage contract $`T`$ is a
cell of the block's activation, allocated when the block is entered, before
its statements,
holding the activation's **uninitialized marker** $`u`$: one fresh object per
block entry, owning the key $`\kappa_u`$ (`[[uninitialized]]`), and the only
objects that own it. This is a representation invariant, an obligation of
the lowering: every string key a JavaScript object has is represented
under $`\mathsf{esc}`$, whose image misses the model's reserved spellings
(`reservedSpelling_escapeKey`, [keys](SEMANTICS.md)); the model's own
reserved keys (`[[proto]]`, `[]`, `[[code]]`, `[[host]]`, a class's
prototype key) are other spellings; and no allocation but the marker's,
source, native or host, adds $`\kappa_u`$, so no source-visible value or
object on its prototype chain owns it. `copiedKey` excludes $`\kappa_u`$,
as it excludes `[[host]]`, though by confinement
([calls through `Function.prototype.call`](#calls-through-functionprototypecall))
no copy receives a
marker. The cell's
contract is $`T\cup U`$, with $`U`$ a label of its own whose one clause
requires $`\kappa_u`$; closures and function declarations capture the cell
itself, never its contents.

#### Checked access

A read of $`x`$ reads the cell once, tests that value
for $`\kappa_u`$ (the calculus's `hasKey`, which is false of a primitive;
never JavaScript's `in`, which throws on one), throws on the true edge, and
on the false edge proceeds with the same value, the test's slice removing
$`U`$ (`tagSlice`), so at $`T`$:

```math
\frac{\Gamma\vdash x:\mathsf{cell}(T\cup U)}
     {⟦x⟧=\mathsf{let}\ v=\mathsf{read}(x)\ \mathsf{in}\ \mathsf{if}\ \kappa_u\in v\ \mathsf{then}\ \mathsf{throw}\ \iota_{\mathsf{RE}}()\ \mathsf{else}\ v,
      \qquad \Gamma\vdash ⟦x⟧:T\ \text{on its normal edge}}\ \textsf{early-read}
```

Only checked accesses read the cell, so the marker never reaches a value
position: a return, an argument, a spread, a copy or a serialization. The
operators keep ECMAScript's order: `x = e` evaluates `e`, then checks, then
writes; `x += e`, an update and a logical assignment begin with a checked
read; `typeof x` is a checked read followed by the test. Assigning a `const`
is refused by TypeScript and is outside the fragment.

#### Initialization

The declaration's evaluation, where the source has it,
writes its initializer's value into the cell after the initializer
completes normally, checked at $`T`$; `let x;` writes `undefined`. An
initializer that throws leaves the marker, so a closure retained from that
activation throws at every later read, as JavaScript's does.

#### The throw

$`\iota_{\mathsf{RE}}`$, `%ThrowUninitialized%`, allocates a
`ReferenceError` by the realm's intrinsic constructor, whatever a source
binding of that name holds, and throws it: the read's exceptional edge,
which reaches the enclosing handler as any throw does, with no fact of the
normal edge. Its footprint is empty over storage that existed before it;
effects already performed, by an assignment's right side for one, remain.

#### Precision

A checked read always has its exceptional edge: where the
cell's current contents are known at $`T`$, the test is still undecided for
a $`T`$ that is an open record, a dictionary or `unknown`, and after a call
the cell is again at $`T\cup U`$. Safety, a value, a step or a throw, holds
either way; an exceptional guarantee that excludes the throw would need a
durable initialization fact, which the model does not have.

#### Ownership

The parser marks each early binding in the Fragment
(`markEarly`) and lists `%ThrowUninitialized%` where a file has one; Lean
lowers a marked binding as above, allocating the cells at the list's entry
(an `early` node of the flow graph), capturing the cell and the intrinsic in
every closure that mentions the binding, and lowering every mention as a
checked access, in graph code and in closure term code. A mention of an
unmarked binding before its initialization has no binding in scope there and
is refused by the lowering. The producer proposes $`T`$ and the claims at
the checked accesses; no claim can omit a check, replace the cell by a
value, or make an initialization an unchecked write
(`early-bindings`, `invalid-early-binding-stale`, run under Node; the forged
claims of `pipeline/test.mts`: a dropped contract, a contract narrower than
the annotation, a checked access claimed past the contract). The stated
type $`T`$ is the annotation, or a function literal's parameter and result
annotations; an early binding with neither is refused, and so are the
compound assignment, update and logical assignment of an early `let`, an
assignment to one in closure term code, a key-adding write of an object one
holds, and an initializer that reads its own binding.

### Recursive constants

A constant whose initializer is a function literal,
an arrow or a function expression with nothing else evaluated, reads its own
name inside the literal's body and parameter defaults:
`const visit = (n: Node): R => … visit(child) …`. Creating the literal runs
neither, so every such read runs during an invocation, after the binding
holds the closure. The read is the code's **self entry**: every invocation of
graph code enters it with the invoked object, the exact
$`\mathsf{obj}(\mathit{fs},\mathsf{graph}(\ldots))`$ the call step matched, in
the slot after the captures ([graph code](SEMANTICS.md#graph-code)); a bound
function forwards to its target first, so self is the original closure, never
the wrapper. A nested closure captures the self entry as any other slot. The
literal's code, of fixed arity, is checked from the frame with self at the
closure's claimed type, and the closure rule proves the closure meets that
whole type, its effects and exceptional guarantee included, by induction on
the step index (`funGraphSelf`,
[program typing](PROGRAM-TYPING.md#judgments-and-constructor-views)): at
budget $`n`$ every invocation runs at a lower index, where the induction
hypothesis gives self its type. A read of the self entry is a flow of the
closure like any read of the constant, so where it is expected at a
signature binding more parameters, as `some`'s callback in `const binder =
(t: Term): boolean => t.k === "union" && t.parts.some(binder)`, the closure
is offered that signature ([offers](SOURCE-ELABORATION.md#source-closures-and-their-annotations))
and its claim holds it; the read meets it as a conjunct of the claim
(`recursive-constant-callback`). The producer types the body's reads at the
constant's annotation or the literal's own signature, which its result
annotation completes, beside the signatures it is offered, with the
footprint it proposes for the closure:
every such closure is assumed to change nothing, and rounds of inference
raise the assumption to what the closure's claim then shows, as for
[function declarations](SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification);
the checker derives each from the claimed type. A `find` callback calling
a recursive constant whose body changes nothing is therefore within the
empty footprint, its element `T` (`find-recursive-constant`); one whose
body shrinks the array is the unrestricted callback
(`invalid-find-recursive-constant-mutation`, run under Node), and a
closure whose body writes, claimed at the empty footprint, its self entry
with it, is refused in search and in checking (a control over
`recursive-constants`). A `let` read by its own initializer's closure is a
cell, which a later assignment may rebind, never a self entry
(`invalid-find-recursive-cell`, run under Node). Every
other read of a binding in its own initializer is refused at its location
(`recursive-const-before-initialization-refused`), and module initialization
order is checked by `Sites.checkInitializationOrder`.

### Module cells

A module-level `let x` that the module does not export,
in no form (no `export let`, no `export { x }` or alias of it), is an
[early binding](#lexical-bindings-before-initialization) of the module's
scope, whatever its mentions: a **module cell**. The initialization unit
allocates it at its entry, before any statement and before the module's
functions and classes exist, holding the module's uninitialized marker,
and binds a module constant to it, so a closure or function created before
the declaration captures the one cell, as `const get = () => x; let x = 1;
get();` needs. The declaration writes the initializer's value after it
completes normally; `let x;` writes `undefined`. Every mention of $`x`$, in
the initialization unit, in every module function and in every closure, is
a checked access, so a run that reaches $`x`$ before its initialization
throws the `ReferenceError` JavaScript throws, and no initialization order
check is needed for it:

```math
\frac{\mathtt{let}\ x\ \text{at the module's top level, not exported}\quad C_x\ \text{its one contract}}
     {\Gamma_f(x)=\mathsf{cell}(C_x\cup U)\ \text{for every unit } f\ \text{of the module}}\ \textsf{module-cell}
```

$`\mathsf{cell}(C)`$ is the private cell's invariant writable field at
$`C`$. $`C_x`$ is one contract for the binding, stated once in the claims
and the same in every unit: its annotation. The module's units read the
binding, so it is a unit boundary, whose type is written, as a module
function's signature is; an unannotated module `let` is refused at the
gate (`invalid-unannotated-module-let`). The initialization unit checks
the initializer against $`C_x`$, and every unit each of its writes,
`undefined` included for `let x: T;`; no unit narrows it. A unit's theorem assumes $`x`$ at
$`\mathsf{cell}(C_x\cup U)`$, its contents any value there at the unit's
entry and after each call; the facts a unit establishes of the contents
follow the [current-content rules](PROGRAM-TYPING.md#current-content-rules-semantic-layer):
a write or a call ends them, a join keeps only what every edge proves, and
a closure captures the cell's identity, never its contents. Composing the
units' theorems for a module execution, with the cell's contract as a
shared invariant of the heap every write preserves, is
[module composition](../WORK.md#module-composition). A `var`, whose binding
exists from the module's entry at `undefined` and may be redeclared, and an
exported `let`, a live binding importers read, are outside the fragment. A
module `let` stays a cell whatever writes it; a certified module's run checks the initialization that
allocates and initializes its cells with the module's units
(`module-cells`, `module-cell-before-initialization`,
`module-cell-saved-value`, `invalid-module-cell-stale`, run under Node;
`certified-module-cell-value-import`; a cycle of modules whose
initialization reads a cell of a module not yet evaluated throws at the
checked access, `certified-cell-cycle-value-import`, run under Node; the
forged claims of `pipeline/test.mts`: a dropped or narrowed contract, a
narrowed entry claim, a read after a writing call claimed at the earlier
value).

### Module functions

A module function is an immutable slot holding its code. A file without
imports or exports may run as a script, whose top-level functions are
properties of the global object other scripts can write; the slot rests on
the trusted assumption that other code preserves the file's top-level
bindings and their functions (the file runs as a module, or no other code
writes its globals or gives one of its functions an own `call`, `apply` or
`bind`), for a plain call
and for `.call`, `.apply` and `.bind` alike
([trust surface](DESIGN.md#trust-surface)).

## Source closures and their annotations

A source closure `(x₁: D₁, …, xₙ: Dₙ): Rₛ => t` is checked at the arrows its
claim names, by the creation rule of [program typing](PROGRAM-TYPING.md#functions-calls-and-receivers): each claimed
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
types them; an enum member's literal type at the value the enum's
interpretation gives it; and an anonymous record as an object contract. A
named declaration's instance is the reference at the instance's arguments,
the declaration read as written with each binder at its argument, so
`Box<T>`'s `v?: T` is `v?: number`, `v?: number | undefined` and `v?: never`
(absent only) at `number`, `number | undefined` and `never`
(`closure-contextual-optional-instances`). A type TypeScript gives with the
name of a program's declaration, an alias of a union included, is read as
that reference, before its structure: a recursive alias such as `Json`
closes at its name (`closure-contextual-recursive-alias`), and a type reached
again within its own structure through no declaration's name is refused. A type literal or mapped type the
program writes is read as written, by the annotation reader, where
TypeScript gives it outside any generic declaration or at its declaration's
own binders. Any other record (an object literal's type, a library mapped
type's instance such as `Record<string, unknown>`, a generic declaration's
anonymous record at an instance) is read member by member: a member of its
own type literal at its written modifiers, and at its written type where
that names no binder; any other at the type TypeScript instantiates,
readonly where the instantiation makes it so. An optional member at an
instantiated type is refused, save an object literal's at `undefined` alone
(an array literal's records, each given the others' members so): the
compiler's API gives an anonymous record's instance no instantiation of its
declaration's binders, and the member's type carries the `undefined`
optionality adds, from which the written contract is not recovered
(`closure-contextual-anonymous-instance-refused`,
`closure-contextual-nested-instance-refused`). Each index signature is read
by its key, string, number or symbol, with its capability. A method, an
accessor, a symbol key or an index of another key of such
a record is refused at the parameter (`closure-contextual-records`,
`closure-contextual-method-refused`). A tuple with an optional position is refused, since TypeScript
gives that position's type with `undefined` whether or not an annotation
wrote it (`invalid-contextual-optional-tuple`). A callable object is read
through its signature before the member-by-member record reading. A function type is read as a
record's type literal is: one the program writes, as written, by the
annotation reader, where TypeScript gives it outside any generic declaration
or at its declaration's own binders. Any other callable without members (a
generic declaration's function type or callable type literal at an instance, a library's, a
function's `typeof`) is read through the one call signature TypeScript
instantiates, at the ordinary effect an annotation of it states, which
assumes no preservation of the heap:

```math
\frac{\tau\ \text{has exactly the call signature}\ (\mathit{this}{:}Q;\ x_1{:}A_1,\ldots,x_n{:}A_n,\ \ldots r{:}E[\,])\Rightarrow B\ \text{and no binder, other signature or member}}
     {\mathrm{ctx}(\tau)=(\mathrm{ctx}(Q);\ \mathrm{ctx}(A_1),\ldots,\mathrm{ctx}(A_n),\ \ldots\mathrm{ctx}(E))\to_{\mathsf{ord}}\mathrm{ctx}(B)}\ \textsf{contextual-callable}
```

A rest typed by a tuple of required positions $`[E_1,\ldots,E_k]`$ is those
$`k`$ further parameters at $`\mathrm{ctx}(E_1),\ldots,\mathrm{ctx}(E_k)`$,
and a rest typed by an alias is read through the alias's equation, as a
written rest is. The receiver is read where the signature states one
(`closure-contextual-callable-receiver`), an optional or defaulted parameter
at its signature's parameter type, which holds the `undefined` an omitted or
explicit argument gives, and a promise `x is T` or `asserts x is T` about a
parameter as a second form at the promise's effect and type, as the
annotation reader reads a guard. Refused at the parameter, as contracts the
reading does not recover: type parameters
(`closure-contextual-callable-generic-refused`), a promise about the
receiver or without a type, a rest of another type, a construct signature, a
second call signature and a member beside the call signature
(`closure-contextual-callable-members-refused`). The reading is the
annotation the closure is checked at, and the closure is checked where it
flows at the signature it is offered: a closure calling its callable
parameter with a number is no handler of a signature passing a function of
strings alone (`invalid-closure-contextual-callable`, run under Node;
`closure-contextual-callable`, `compiler-api-contextual-callable`).

A contextual parameter type is a proposal like any claim, since the body is checked at
$`A_j\sqsubseteq_G D_j`$ and the closure at $`\bigwedge L`$ wherever it goes, the
call offering it included. A closure is **offered** each signature binding
more parameters than it does that is expected where it flows: passed where
a callback is offered more parameters (`xs.reduce(acc, null)`), bound under
such an annotation directly, through an alias or through another binding,
returned at such a result. It is claimed where it is created at that
signature beside its own, and its code is checked at each (`CodeOffers`),
the premise over $`L`$ above keeping each claimed parameter within its
annotation:

```math
\frac{\lambda(\vec x{:}\vec D).t\ \text{flows to a position expecting}\ (R;\vec A)\to B\quad |\vec x|<|\vec A|}
     {(R,\vec A,B)\in L}\ \textsf{offer}
```

A [recursive constant](#recursive-constants)'s closure
flows wherever its body reads its self entry, which holds the closure: a
read of $`f`$ in $`t`$ where $`(R;\vec A)\to B`$ is expected puts that
signature in $`L`$ by `offer`, and the code is checked at every row of
$`L`$ with the self entry at the whole claim, so the read meets the
signature as a conjunct:

```math
\frac{\mathsf{const}\ f=\lambda(\vec x{:}\vec D).t\qquad
       \forall(R,\vec A,B)\in L.\;\Gamma,\ f{:}\textstyle\bigwedge L,\ \vec x{:}\vec A_{\le|\vec x|}\vdash_G t:B}
     {\Gamma\vdash_G \lambda(\vec x{:}\vec D).t:\textstyle\bigwedge L}\ \textsf{offer-self}
```

The premise abbreviates `CodeOffers` with the self entry at $`\bigwedge L`$:
each row's check covers its effect and exceptional guarantee, the
parameter defaults' execution, the receiver, each claimed parameter within
its annotation, and a variadic row's fixed parameters covering the
closure's. This is `funGraphSelf` at a claim holding offered rows:
`t.parts.some(binder)` in `binder`'s own body, a default reading the
constant, a bound wrapper and a variadic row
(`recursive-constant-callback`); a self read at a longer signature does not
carry the closure's preservation onto its exceptional edge
(`invalid-recursive-constant-exceptional`, run under Node). The producer
proposes the offered rows for the self entry of a plain closure, without
type parameters, a rest or a written promise; the self entry of any other
is read at its own signature, so its self read at a longer signature meets
none and is refused (`recursive-guard-callback-refused`, a gap). A self read where a
signature with a parameter outside the closure's is expected is not
offered and meets nothing, so it is refused, called at once or stored and
called later with more arguments, both admitted by TypeScript, which
compares a method's parameters both ways
(`invalid-recursive-constant-self-wider`,
`invalid-recursive-constant-escape-wider`, run under Node). A self read
passed to `find` by a closure shrinking the array meets only `find`'s
unrestricted callback, at `T | undefined`
(`invalid-recursive-constant-callback-mutation`, run under Node). A `let`
read by its own initializer's closure is a cell, refused as an early
binding (`invalid-recursive-cell-callback`, run under Node), and a name the
body binds again is that binding, a value known by its type
(`invalid-recursive-constant-shadowed`, run under Node).

An offered parameter may be narrower than the closure's,
$`A_j\sqsubseteq_G D_j`$ strictly: a closure over a union passed to
`forEach` of an array of one arm is checked at the element. Its code is
checked from an entry at $`\vec A`$, where a test the narrower entry decides
narrows each branch differently than at $`\vec D`$, so each signature's
interior claims are its own (`closure-offer-narrower-element`).

<a id="closure-offers"></a>
The producer proposes an offer where each offered parameter is plausibly
within the closure's, by a proposal heuristic modelled on Lean's relation
and read up to the declarations: a union
arm by arm, and a record by width and depth as the
[record rule](POSITIVE-TYPES.md#clause-coverage) reads it, each member of
the parameter met by the element's member of its key, an invariant field by
an equal invariant field, a view by a required member within it, an optional
member by a slot within it, excluding required readonly `length` views,
a writable one by an equal writable slot, a
method by a method within it, with contravariant receiver requirements
and every target stable key stable in the source. A value with call
signatures is never within a record without any, and width and depth apply
within one clause kind: a record without call signatures within such a
record, a callable value with fields within one with fields or within
signatures alone, signatures alone within signatures alone, an array within
an array. Each writable target index
also preserves every overlapping source index contract and optional field
or optional readonly view; the heuristic conservatively treats every string
key as potentially numeric for this check. An interface extending
another is within its base where its overriding members are within the
base's (`closure-offer-extends`), and a compiler-API `Expression`, whose
residual arm holds a brand beside the members of `Node`'s, is within `Node`
(`compiler-api-closure-offer-node-list`). Lean
decides inclusion and checks each offered row. An element whose method
requires a stronger receiver or takes a narrower
parameter, a look-alike of a family shape and a function over a narrower
parameter widened through a method signature are refused
(`invalid-closure-offer-extends-receiver`,
`invalid-closure-offer-extends-method`,
`invalid-compiler-api-closure-offer-lookalike`,
`invalid-closure-offer-extends-narrower`), and a closure shrinking the
array meets `map`'s signature with holes
(`invalid-closure-offer-extends-mutation`), each run under Node.

A guard closure, one whose result annotation writes a promise
$`x_p\ \mathsf{is}\ T`$, is offered a promise signature stating that
promise at the written type, and is claimed at it with the promise; the
promise goal checks its body there as at its own arity
([user-defined guards](#user-defined-guards)):

```math
\frac{\lambda(\vec x{:}\vec D)\colon x_p\ \mathsf{is}\ T\Rightarrow t\ \text{flows to a position expecting}\ (R;\vec A)\to T'\,[\mathsf{guards}\ p]\quad |\vec x|<|\vec A|}
     {(R,\vec A,T)\,[\mathsf{guards}\ p]\in L}\ \textsf{offer-promise}
```

Of a callee's signatures (`filter`'s plain and guard ones), a guard closure
literal is expected at those whose callback states its written promise,
where any does, each binder that promise's type determines read at it; any
other closure, and a guard closure no signature's callback states the
promise of, at those whose callback states none. The producer proposes the
call at a signature stating a guard closure's promise before the others, a
search order only: Lean checks the selected signature and every argument.
A promise signature promising a type meets one promising a larger type
(`TypePromise.result`), so a result expected at a wider type keeps the guard
overload (`guard-closure-callback`). A promise at a signature binding more
parameters is met only by code checked there, so a guard read as a value
meets only the plain signatures.

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

`f.call(r, ā)`, `f.apply(r, l)` and `f.bind(r, ā)`, where TypeScript binds the member to the standard library's `call`, `apply` or `bind`, are the standard methods
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

## Inferred call effects: elaboration and certification

A call signature states a [closed footprint](FOOTPRINTS.md#changes-and-footprints):
on normal return, the call changes the contents of the previously allocated
locations holding a value and of those holding an array store at most as it
says. The empty footprint leaves every such location's contents unchanged;
`all: any` constrains none. It may allocate fresh storage. A type guard's and
an assertion function's signatures state, besides, the promises `guards` and
`asserts`, a promise about an actual
([user-defined guards](#user-defined-guards)). An
**effect-qualified signature** is a signature carrying such a guarantee. `CallEffects.lean` defines its semantics; the
[effect contract](SEMANTICS.md#effect-qualified-call-contracts) and
[certification rules](#definition-and-application-rules)
state what a certificate must establish.

This extends the language of claims beyond TypeScript annotations. Three
operations must remain distinct:

1. **Annotation translation** preserves the source contract. An ordinary
   TypeScript arrow imposes no heap-preservation guarantee. It must never become
   an effect-qualified arrow merely because a consumer needs one.
2. **Inference** proposes a stronger type for a definition, including an effect
   on each call signature. This is untrusted producer work. It can use bodies
   and inferred contracts of callees; it need not change the source annotation.
3. **Elaboration and verification** attach the proposal to the lowered
   definition and discharge its additional obligation. Lowering emits proof
   obligations; it does not establish an effect by translating syntax. Lean must
   check both ordinary body safety and the claimed effect, with the original
   annotation obligations retained. Only certified types may justify uses.

At a call, the rule consumes the qualified type of the value. It does not
inspect its source body or recheck it for the observed call. The guarantee
must survive passing, returning, capturing and generic instantiation through
ordinary type operations. An explicit annotation may forget the guarantee;
that loses precision, not soundness. Overloads carry effects per signature.
An imported implementation needs checked evidence
([certified imports](SOURCE-CONTRACTS.md#certified-imports)) or an explicitly documented external
assumption: its TypeScript declaration supplies neither proof nor an implicit
effect. Built-in contracts remain separately audited assumptions.

### Calls through a location

A call consumes the contract established for
the callee value; a stronger effect needs a certificate, and storage keeps
its checked lifetime contract. A module function declaration no code
reassigns is read at the signature certified from its body
([function declarations](SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification)),
as a certified import is. A field or element read, `e.f(…)` or `e[k](…)`,
gives the value the location holds when the call runs: one written after
any initialiser, through any reference, or held by a record built
elsewhere. The callee is read at the location's contract, checked at every
write: the lowering of its declaration, with the effect that declaration
states, or, for a fresh literal's field no contextual type fixes, the
storage contract inferred from its initialiser, which keeps a certified
signature's effect and widens a literal's type. An annotation states the
effect its [statement](#stated-effects) states, `Within<F, T>`, and none
without one, `typeof f` of a function declaration included, which names
`f`'s declared signature. With
$`\epsilon`$ the contract's effect,

```math
\frac{\Gamma\vdash e:\{f:\mathcal F_\epsilon(R,\mathcal A,B),\ \ldots\}\qquad
      \Gamma\vdash e:R\qquad\Gamma\vdash\vec v:\mathcal A}
     {\Gamma\vdash e.f(\vec v):B\;!\;\epsilon}\ \textsf{field-call}
```

`readonly` grants no more: it is a view, and a record holding any function of
the field's type has the class's type. A `findIndex` callback calling a
function held by a field whose contract is an ordinary arrow is therefore
the unrestricted one, its element
`T | undefined` (`invalid-field-call-effect`,
`invalid-readonly-field-call-effect`, run under Node); a write of a
function that does not keep storage into a literal's field or a cell whose
inferred contract does is refused (`invalid-field-call-effect-alias`,
`invalid-field-call-effect-cell`, run under Node); a callback calling a
module function, directly or through a fresh literal's field, verifies at
`T` (`find-index-module-function`).

The first guarantee preserves existing heap contents on normal return and
allows fresh allocation. A call that throws supplies no heap postcondition.
Consequently, a body checker cannot carry this guarantee through a caught
exception: it must check the handler with the possibly changed heap, or have
a separately justified guarantee for exceptional exits ([exceptional footprints](#exceptional-footprints)). The pure-body
checker does not admit such calls. Graph composition checks normal-return
postconditions node by node and refuses handlers; the independent pure-graph
rule can still certify pure handlers. Qualified-call composition retains
this distinction. No stronger external assumption is implicit here.

The guarantee is sufficient but not necessary for safe dense
`map`: mutation of unrelated state can also be safe. [Footprints](FOOTPRINTS.md)
designs effects that express that within the same inference/certification
boundary.
The body-effect checker recognizes a subset of programs satisfying the
semantic contract. An unrecognized body therefore represents an inference or
checking limit, not a restriction on the meaning of heap preservation.

The source acceptance theorem includes effect checking. Pipeline controls
exercise qualified callbacks passed or returned as values, ordinary-call
fallbacks, and forged effect claims on bodies that mutate captured storage.

### Definition and application rules

The semantic foundation is
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

Source acceptance runs this checker, and `SourceClaimJson.checkJson_safe`
states its conclusion. One contract record carries receiver,
arguments, result and required effect through graphs, claims and certificates;
subtyping checks effect implication and substitution preserves it. Ordinary
source annotations remain unrestricted; OCaml proposes preservation for
closure bodies of reads, element reads, fresh allocations, patterns without a
rest, and fixed calls and method calls whose callee's signatures all state it
(`footprint_expr` in `source.ml`), retaining it through symbolic claims and
substitution. Evidence production adds a
code entry to its search table only after the complete body/effect check passes.
A forged effect thus fails at the defining callable's located typing obligation.
All code certificates remain in the submitted response, and final acceptance
independently checks every one; withholding a search hint cannot hide a failure. Qualified graph claims are
submitted and certified through the ordinary source pipeline.

### Function declarations

A declaration's claim states the closed
footprint $`\Phi`$ proposed for its signature (`footprint` in the
[claims](SOURCE-CLAIMS.md)). The unit of a declaration claiming a footprint
other than `all: any` is checked as a code entry's graph is: its nodes pure,
or each node within $`\Phi`$ on normal return (`effectResult`, alongside
ordinary safety), under the ordinary checker, at the unit's goal: a plain
result, a guard's promise or an assertion function's. A node is
within $`\Phi`$ as an inspection, which preserves the heap; as a write of a
field every alternative of the object's type gives a type of source values,
within `{value: any, store: keep}` since the location holds a value
(`ExpressionEffects.write_within`); or as a fixed call at a selected signature
whose footprint is within $`\Phi`$. Runs within a closed footprint compose
(`Closed.Holds.trans`), so the graph is (`GraphCode.goto_bounded`), its
return meeting the goal. A guard's or an assertion function's promise
signature states its footprint beside the promise (`moduleArrow`;
`guard-footprint`, `invalid-guard-footprint`). A unit qualified by a
resolution descriptor is refused such a claim. A code entry's signature
follows the same rule (`GraphCode.effectCheckedResult`), a guard closure
claiming no footprint. With $`P`$ the unit's graph, $`\Gamma`$ its
inputs and $`B`$ its result,

```math
\frac{\vdash P:\Gamma\to B\qquad \forall l.\ P_l\ \text{pure, or within}\ \Phi}
     {\vdash P:\Gamma\to B\;!\;\Phi}\ \textsf{declaration-effect}
```

and `SourceClaimJson.checkJson_safe` states, for each such unit, that its
graph run as code from inputs it admits returns with a heap its claimed
footprint relates to its entry heap, and a value meeting its goal
(`SourceExtraction.checkRequests_footprint_at`).
Every other unit reads the declaration at its annotation's signature stating
that effect, its variadic extension included (`moduleArrow`), as it reads the
declaration's ordinary signature: that each declaration meets the signature
the others read it at is the [module composition](../WORK.md#module-composition)
argument. A parameter default executes in the declaration's graph, so the
check covers it. An imported function is read at its declaration's type,
which states the effect its [statement](#stated-effects) states and none
without one (`invalid-preserving-callback-value-import`). OCaml
proposes the effect at the greatest fixpoint over the module: every
declaration whose body could preserve the heap, were its callees to, is
assumed preserving, recursion included, and rounds of inference withdraw the
assumption from each whose claims then do not show it; a body calling a
quantified callee at an instance is not proposed. A forged effect fails at
the first node that does not preserve the heap, in evidence production and
in checking (`declaration-preserving-callback`,
`invalid-declaration-write-callback`).

### Stated effects

A written signature's result annotation may state the signature's effect:
`Within<F, T>`, with `Within` the verifier's declaration in
[`tools/resolvable.d.ts`](../tools/resolvable.d.ts), which TypeScript reads
as `T`. A reference is a statement where TypeScript binds its name to that
declaration, never by its spelling: an alias of the repository's file, or of
a file of exactly its bytes, which declares the same aliases (the census's
copy of `tools/` holds one). $`F`$ is a type literal written in place,
`{ value: "keep" | "any"; store: "keep" | "grow" | "any" }`, with
`onThrow: true` where the footprint holds on a throw too. With
$`\epsilon(F)`$ the effect of that closed footprint and flag, no promise, no
fresh result and no receiver-store exception,

```math
\frac{⟦\vec A⟧=\vec P\qquad ⟦T⟧=B\qquad F=\{\mathsf{value}{:}\,v,\ \mathsf{store}{:}\,s[,\ \mathsf{onThrow}]\}\qquad \{v,s\}\neq\{\mathsf{any},\mathsf{any}\}}
     {⟦(\vec x:\vec A)\Rightarrow\mathtt{Within}\langle F,T\rangle⟧=\mathcal F_{\epsilon(F)}(R,\vec P,B)}\ \textsf{stated-effect}
```

The written signatures are a function declaration's, a class's instance or
static method's, an object literal's method's, an arrow's, a function
expression's, a function type's, and an interface's or a type literal's
method or call signature. Every reader of a signature, the declaration
reader for a declaration a type reaches and the gate for a definition it
lowers, reads it through one function (`statedResult` in
`tools/type-term.mts`), so `typeof f` reads `f`'s statement too. Refused,
each where it is read ([fragment boundary](SOURCE-FRAGMENT.md)): `Within`
anywhere else, a reference the declaration reader resolves to `Within` or
`Footprint` outside a signature's result included; a footprint written
other than in place; the footprint letting everything change, with or
without `onThrow`, which states nothing; a statement on an async
definition, whose call returns where its body throws
([async](#definition-and-application-rules)); on a constructor or a
construct signature; on any signature of an overloaded declaration, whose
unit is certified at one; on a declaration with a resolution-qualified
type parameter, whose unit claims no footprint; on a generic closure or
method, whose code is checked at the binder bounds its claim states, which
need not cover its own; and a statement written
outside the program's sources (a declaration file, a package, an ambient
declaration) or reached from the type of a value declared there, through
`typeof`, an alias, an interface or an indexed access, other than a member
of a class the program declares: such a value's code is the environment's.

**Certification.** A definition stating $`\epsilon`$ is certified at it
from its own code, whether or not any code calls it, and before any other
check of its effect. A declaration's claim lies within its statement, its
unit is certified at its claim, and the unit's inputs are its annotated
parameters, so the certification covers the written signature's whole
domain:

```math
\frac{\vdash P:\Gamma\to B\;!\;\Phi\qquad \Phi\le\epsilon.\mathsf{footprint}\qquad \epsilon.\mathsf{onThrow}\Rightarrow\mathsf{onThrow}(\Phi)\qquad \mathrm{completion}(d)=\mathsf{sync}}
     {\vdash d:\Gamma\to B\;!\;\epsilon}\ \textsf{stated-declaration}
```

(`RequestJson.statedWithin`; proved: `SourceRequests.effectResult_stated`,
`SourceRequests.checkRequests_stated_at`, from `checkRequests_footprint_at`
by `Closed.Holds.mono`). A claim may offer a closure at signatures narrower
than its annotation, so a closure's statement is proved as a written
promise is, whatever the claim offers: some row $`\rho`$ its code is
checked at admits the annotation's whole domain, receiver $`R`$, arguments
$`\vec A`$ (a defaulted one with `undefined`) at its arity, returns within
the annotated result, and has an effect covering $`\epsilon`$:

```math
\frac{\rho\in\mathrm{rows}(c)\qquad R\subseteq\rho.\mathsf{receiver}\qquad \vec A\subseteq\rho.\vec{\mathsf{args}}\qquad \rho.\mathsf{result}\subseteq B\qquad \rho.\mathsf{effect}\ \mathrm{covers}\ \epsilon\qquad \vdash\mathrm{code}(c):\rho}
     {\vdash c:\mathcal F_\epsilon(R,\vec A,B)}\ \textsf{stated-closure}
```

(`lambdaSetup`'s statement obligation; the code at $`\rho`$ by
`GraphCode.codeChecked_sound`, the statement by `Effect.covers_sound`). A
closure with no such row, one claimed at no call signature included, is a
located refusal (`invalid-method-effect-unused`). A closure collecting a
rest array is checked at its annotation's own signature, whose effect is the
statement. A class's instance type holds each method's statement, so its
construction, checked at the instance type, finds each method on the
prototype at a contract whose coverage compares effects, and an override is
checked against its base's statement (`invalid-method-effect-override`); a
static method's binding is checked at its annotation. Every other value at
a stated type meets it by the existing introductions: a field write is
checked at the field's contract (`invalid-method-field-effect-write`), a
value passed where a stated member is expected by subtyping
(`invalid-method-effect-lookalike`), an input by `EnvOk`.

**Over the whole domain.** A statement on `m(this: C, …)` holds for every
receiver of type `C`, so every call in `m`'s body is at a contract stating
an effect within it; a call of an unstated member of `C`, which a value of
`C` may hold any function in, defeats it
(`invalid-method-effect-unstated-dependency`, run under Node). Lean checks
each call at its selected signature wherever it certifies the definition.

**Across modules.** A statement read from an imported declaration is part
of its type, so the importer relies on it under the import assumption
([trust surface](DESIGN.md#trust-surface)), as on any declared type: the
importer verifies relative to it whether or not the exporting module's run
certifies it (`stated-assumed-value-import`, whose control runs the
exporting module's refusal). A certified import's unit claims within its
statement. A census slice's own definitions are a copy of its module's, so
a verified slice certifies their statements relative to the statements of
what it imports.

**Producer.** OCaml proposes, for a stated definition, the footprint its
body shows where that is within the statement, and the statement otherwise,
which Lean then checks node by node; a stated declaration is assumed at most
at its statement while the module's footprints are inferred
(`within_statement` in `ocaml-producer/source.ml`). Callees' statements
reach it through their types, as natives' footprints do.

### Exceptional footprints

An effect may promise that its footprint also holds when the call throws:
`onThrow`. The promise covers the heap a throw leaves the call in, from the
call's entry heap, exactly as the footprint covers a normal return's. It says
nothing of the thrown value. A handler of a node calling at such a signature
then starts in a heap the footprint relates to the node's entry heap, and a
body that catches can be certified at a footprint.

#### Semantics

`SafePost Ξ T Q` states `Q` of the heap a value is returned in
and nothing of a throw. Its generalization `SafePostExc Ξ T Q R` states, in its
throw disjunct, `R h` of the heap `h` at which the term raises, whatever
value it raises:

```math
\mathsf{SafePostExc}\,\Xi\,T\,Q\,R\,(n{+}1)\,W\,h\,t \iff
(\mathsf{val}\,t \wedge T\,W\,t \wedge Q\,h\,t)
\vee (\exists v.\ \mathsf{Raises}\,t\,v \wedge \mathsf{Scoped}_0\,v \wedge \Xi\,W\,v \wedge R\,h)
\vee (\exists W'\,h'\,t'.\ \ldots \wedge \mathsf{SafePostExc}\,\Xi\,T\,Q\,R\,n\,W'\,h'\,t')
```

with the step disjunct as in `SafePost`. `SafePost Ξ T Q` is
`SafePostExc Ξ T Q (fun _ => True)`, and `erase` holds for both. An
effect $`e`$ with `onThrow` gives the arrow's run, from entry heap
$`h_0`$, the exceptional postcondition
$`R\,h \iff e.\mathsf{footprint}.\mathsf{HoldsOn}\,P\,h_0\,h`$, with
$`P`$ the locations its `receiverStore` leaves bounded, as `Effect.within`
reads them. Without `onThrow`, $`R`$ is `True`. In coverage
(`Effect.Covers`), an effect with `onThrow` covers one without, and not the
other way.

#### Combining effects

Two guarantees of one call combine
(`Effect.meet`) into the meet of their footprints, with `onThrow` the
conjunction of theirs. A disjunction would be unsound: an empty footprint
stated on normal return only, met with a wider one stated also on a throw,
gives no empty footprint on a throw. Where the conjunction loses a useful
guarantee, the signatures stay separately selectable, as overloads are. The
field is carried, and audited, wherever an effect is: overload combination,
weakening by an annotation, `bind`, construct signatures, and imported and
library signatures.

#### What stays on normal edges

A promise (`guards`, `asserts`) is a fact
about the arguments a normal return establishes, and `fresh` a fact about
the returned value. A throw establishes neither, so neither moves onto an
exceptional edge. A handler binds the thrown value at the graph's exception
family, `unknown`, and the thrown slot is never fresh; the slots the node
already held keep their freshness (`handlerFresh`; the candidate facts
`inferFresh` proposes flow along handler edges the same way). The handler
receives no current-content fact ([handler facts](#exceptional-footprints)).

#### Composition through a body

`GraphCode.BoundState` states the run's
invariant from the body's entry heap $`h_0`$, with $`b`$ the body's
freshness cutoff, the length of $`h_0`$: a node's run is bounded on the
locations below $`b`$, so a node may change storage the body allocated
before it, a receiver among them. Throws keep that cutoff:

- a node with a handler is admitted when its term's run is `SafePostExc`
  whose exceptional postcondition relates the node's entry heap to the heap
  it raises in on the locations below $`b`$; the `handle` transition then
  keeps $`\Phi.\mathsf{Holds}\,h_0\,h`$ by `Closed.Holds.trans_on` with
  the invariant at the node's entry, as `enter` does for a normal return;
- the state `.raised v` keeps $`\Phi.\mathsf{Holds}\,h_0\,h`$ where the body
  claims `onThrow`; without it the state stays unconstrained;
- the `handle` transition also establishes the handler target's
  `FreshOk`, through the handler's slot mapping with the thrown slot
  non-fresh;
- each node's term is checked, on its throws too, by the form that admits
  it (an inspection, a typed write, a call at a selected signature).

#### Handler facts

Ordinary graph certification checks a handler edge
(`HandlerOk`) with facts that hold in every heap: `handlerFacts` drops heap
observations, whatever the throwing call's footprint. A handler therefore
receives no current-content fact across a throw, and one that relies on a
fact the guard before the call established is refused
(`invalid-exceptional-handler-fact`, run under Node). The bounded run's
footprint and freshness are what the exceptional postcondition carries to a
handler. Keeping the facts a throw's footprint keeps would thread the
postcondition through expression checking, `HandlerOk` and `StateOk`.

Every way a node's term can raise is then covered:

- **Before the invocation.** Source lowering evaluates operands into slots
  first (`valueTerm`), so a call node raises either while reading its
  operands, which writes nothing, or in the callee. An inspection may
  allocate before it raises; it preserves the heap's prefix
  (`inspect_step`), so every location below $`b`$ keeps its contents. A typed
  write raises before it writes.
- **In the callee.** A call at a selected signature raises within the
  signature's `onThrow` footprint. In bounded certification, a node whose
  call lacks `onThrow` admits no handler, and a body containing one claims
  no `onThrow`; ordinary safety keeps every handler.
- **Defaults and intermediate mutations.** A parameter default runs as nodes
  of the declaration's graph, and earlier nodes' normal returns compose into
  the invariant, so a throw at any node is relative to the body's entry
  heap.
- **Handlers and rethrows.** A handler is a node like any other. A rethrow
  is a `throw` node without a handler, which raises at its entry heap and so
  reaches `.raised` with the invariant.

A pure graph keeps its independent operational rule, which covers its
handlers already and bounds its throws too: every step keeps the heap a
prefix (`CallEffects.prefix_safe_exc`). A node whose entry has a slot of a
type no value meets is never entered, so it is within any bound
(`GraphCode.unreachableEntry`; `never-parameter-calls`).

#### What `checkJson_safe` states

Its premise is the exact CLI success
condition. Its first conclusion is plain safety; its second, for each
accepted request with a footprint other than `top`, is a `SafePostExc`
whose exceptional postcondition is the footprint from the run's entry heap
where the request's effect states `onThrow`, and `True` elsewhere.

#### Natives

A native signature states `onThrow` only where its audit
covers every throw: validation errors, failures of the host, and the
operation's own errors. `Error` at a string message and `JSON.stringify` at
a JSON value write nothing they did not allocate before they return or
throw, so each states the empty footprint with `onThrow`
([library globals](SOURCE-CONTRACTS.md#library-globals)). `execFileSync`'s
[restricted form](SOURCE-CONTRACTS.md#library-modules) is audited for it;
its overlay entry in `library-modules.mts` states the empty footprint with
`onThrow`, at options whose optional fields `env?: undefined` and
`shell?: false` the argument's claim must meet. An object literal without a
spread meets them by leaving those keys out, since a literal owns exactly
the properties it writes ([object literals](SOURCE-MODEL.md#object-literals)). A literal
with a spread meets them only where each spread part's claim states the two
keys absent or at those types; leaving them out after an open spread does
not. The entry keeps the unrestricted
form beside it, so a call outside the restricted options keeps its type and
an unrestricted effect.

#### Worked example: commit-records

`commit-records`' `git` calls `execFileSync` at
the restricted options and is certified at the empty footprint with
`onThrow`. `at` catches `git`'s throw and returns `undefined` from its
handler, so it is certified at the empty footprint. `examplesOf`,
`readRecord` and `group`'s `map` callback then compose normal-return
footprints, with the [certified import](SOURCE-CONTRACTS.md#certified-imports) of
`parseRecord`. `node-exec-restricted` shows the first steps, and
`exceptional-footprint-handler` the same composition
for callees that build and throw an error: a declaration, a constant's
arrow, and a declaration whose handler rethrows.

#### Producer and wire

A call effect states `onThrow` in the wire
([source claims](SOURCE-CLAIMS.md)), and so does a declaration's claim beside
its footprint. OCaml proposes it for a closure and, at a greatest fixpoint
over the module, for a declaration whose every node bounds its throw
(`Source.throws_stmts`); a `try` whose block bounds its throws, with a catch
and no `finally`, is within the join of the block's and the handler's
footprints. Implementation: `HeapObservations.SafePostExc`,
`CallEffects.Effect.excPost`, `GraphCode.NodeWithin` (its `thr` flag),
`GraphCode.throwsWithin`, `GraphCode.handlerFresh`, `GraphCode.BoundState`
(its `exc` flag) and `SourceRequests.checkRequests_footprint_at`, whose
statement `checkJson_safe`'s second conclusion is.

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
