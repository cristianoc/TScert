# OCaml claim producer

The producer infers candidate types for a TypeScript program. It reads the
shared source representation, called Fragment, and execution plans supplied by
Lean, then writes SourceClaims. Lean checks the proposed types against the
source annotations and the program's behavior in its model. A successful
producer run means that it produced claims; the pipeline reports `verified`
only when Lean certifies every extracted function.

The shared front end uses TypeScript's parser and project resolution. OCaml
performs its own inference. The producer and
verifier share the source language and execution plans; Lean owns the typing
rules and acceptance decision.

## Try it

The producer needs OCaml 5 and Dune 3 (`opam install dune`) and only the
OCaml standard library. `make build` builds it with the verifier, and
`dune build --root ocaml-producer` alone; [the README](../README.md#try-it)
runs a file through the whole pipeline, whose outcomes
[the pipeline entry point](../docs/DESIGN.md#the-pipeline-entry-point)
lists. A pipeline run gives proof search fuel 12 and each stage a 60 s
limit (`TSCERT_STEP_LIMIT` sets another): operational limits, separate from
the typing rules. `VERIFIER` names a verifier executable built from the same
Lean sources, and `PRODUCER` a producer executable built from these.

For direct use, with a run's artifacts:

```sh
lean/.lake/build/bin/verifier --lower-control-flow fragment.json > flow.json
ocaml-producer/_build/default/producer.exe fragment.json flow.json [qualified.json] > claims.json
ocaml-producer/_build/default/producer.exe --explain fragment.json flow.json
```

`qualified.json` lists the imports the pipeline reads at their certified
effects, each by its local name, its declaration identity, its unit's
footprint and on-throw flag. `--explain` prints the known causes of
proposal failure with source spans: an aid to diagnosis, not a verification
result. A refusal exits 2 with a first line `unsupported: …` and a last line
`end of refusal`. Malformed input and a usage error exit 2 with the same last
line and a first line naming the fault (`JSON byte n: unexpected end`,
`missing field: declarations`, `usage: …`); the pipeline reads a record as
the producer's refusal only when its first line starts `unsupported: `, and
reports any other as a tool failure (`refusalOf` in
[verify-source.mts](../pipeline/verify-source.mts), `producerProtocol` in
[stage-execution.mts](../pipeline/stage-execution.mts)). Any other exception
exits 3 with a first line `error: `.

[dune](dune) declares the library and executable;
[dune-project](dune-project) makes this directory a Dune root.

## Execution and inference

A program has three relevant representations:

1. **Fragment** retains expressions, statements, annotations and source spans.
2. **Execution plans** specify control flow, evaluation order and binding order.
3. **SourceClaims** proposes types and environments at points in those plans.

The [languages index](../docs/LANGUAGES.md) identifies their definitions, and the
[claims protocol](../docs/SOURCE-CLAIMS.md) defines their wire format.

Lean constructs the execution plans from Fragment before reading claims. A
statement graph supplies successors, lexical scopes and exception handlers.
Each body has its own graph. Declarations with several bindings have one node
per binding, so an initializer sees the bindings initialized before it.
Expression plans save intermediate values and specify conditional evaluation,
receiver and method evaluation before call arguments, assignment references
and spreads. Binding plans specify destructuring reads, defaults and the
progressive initialization of parameters.

The producer interprets these plans to compute point states. It uses a work
queue: a changed input state causes a node to be visited again, and outgoing
states are joined at successors. Scope projection retains only live bindings;
impossible paths do not contribute types to a feasible join. Exception edges
conservatively forget mutable contents and field facts. Repeated visits can
widen a state by forgetting those facts. Claims for each node come from its
latest transfer, and the producer assembles them after the work queue settles.

Expression inference also reads the source tree to obtain contextual types,
choose callable signatures and infer generic instances. The execution plan
supplies the environment at each observed child expression. Recursive source
typing therefore uses the state appropriate to that child's evaluation, while
the shared plan determines effects and which operands run. Closure bodies use
their own graphs and capture contexts. Each inference pass owns its active
rigid-parameter bounds; a closure extends them for its body and restores the
enclosing scope on success or refusal. Expression-bodied closures use a binding
prologue for defaults; defaults represented as statements follow the body graph.

Analysis state has explicit lifetimes. One producer run owns explanation
observations shared by its functions and retries. Each function owns the
candidate storage contracts passed between inference attempts. Each pass owns
its environments, active bounds, closure offers and collected claims.
`Analysis_state` hides that mutable storage behind an abstract type. The pass
coordinator assembles component inputs from operations declared in
[analysis_capabilities.ml](analysis_capabilities.ml); each component's `Inputs`
signature selects its permitted queries, observations, proposals and scopes.
Components receive immutable values and operations, without the state handle,
shared references or indexing tables. The graph solver receives an owned copy
of the node array; closure setup receives the entry point and binding prologue.

Graph successors carry snapshots of path metadata, and node outputs retain
the claims from the latest visit. Claim-publication operations associate each
claim with the active execution point. Queries distinguish a claim at that
point from the latest claim at a source span, since their consumers require
different lookup semantics.

Speculative inference copies one record containing collected claims, closure
offers and path metadata. `Analysis_state.speculate` restores the enclosing
record on success, refusal and unexpected exceptions, including nested attempts.
Write proposals and explanation observations survive these attempts. A
`Json.Error` refusal returns `None`; other exceptions propagate after restoration.
Node execution collects its output in a named record and restores the enclosing
output and scope-projected path metadata on every exit. Each overload row owns
its expression, entry and storage-contract claims; other inference effects
remain with the enclosing pass. Block return context, observation roots, active
point and rigid bounds use explicit scope operations.

Lean's final lowering consumes the same plan builders, with the claims used
for type-directed operations. It reconstructs plans from Fragment when checking
a proposal. Acceptance depends on the source, claims and certificates; a digest
of the producer's input graph is not an acceptance premise. Source-to-model
correspondence remains a review obligation, described in
[the trust boundary](../docs/DESIGN.md#trust-surface).

## Values, storage and facts

An environment distinguishes a value snapshot from a mutable cell. A cell has
a fixed storage contract and proposed current contents. For example, a cell
with contract `number | null` can hold `number` at one point and `null` at
another. Both writes must meet the same contract. A guard refines current
contents; it does not alter what may be stored over the cell's lifetime.

The producer obtains contracts from annotations or inference. For evolving
unannotated bindings initialized with `null`, `undefined` or an empty array,
it collects candidate types from writes and repeats inference until those
candidates settle. Each function owns its candidate contracts. A pass receives
those candidates and returns the types collected from writes, including writes
observed before a proposal refusal; the next pass can retry with larger
candidates. Additional closure-signature inference retains the settled candidates.
Initializers and every write remain Lean obligations.
Mutable parameters use their annotated contracts. A contract is published
separately from point states, keyed by the binding's initializer span and name;
copies of a declaration in different control-flow paths must agree on it.

Current-content facts cover primitive refinements and exclusions of null,
undefined, or both. Field facts describe an immutable binding's object at a point;
unknown writes or calls invalidate them. Closure analysis forgets facts that
need not hold when the closure runs. The producer's conservative state can
therefore lose information that a stronger analysis might prove. A binding plan
retains the immutable origin of its saved receiver and consults the live field
facts at each read. Each read publishes a type claim that Lean checks before
using the saved result in the rest of the pattern.

Object types distinguish readable fields, writable fields, presence and bounds
on the keys an object owns. Array types distinguish element contracts, tuple
positions, mutability
and presence: dense, readable or sparse. Source `T[]` requires readable elements
in `T`; holes are compatible only when `T` admits `undefined`. A readonly view
is a capability restriction, not a guarantee that another alias cannot mutate
the array. The semantic rules for those distinctions belong to
[positive types](../docs/POSITIVE-TYPES.md) and
[program typing](../docs/PROGRAM-TYPING.md).

## Generic-call inference

A generic declaration binds rigid type parameters: each parameter stands for
one fixed type within its body. Their identities include
scope and index, so nested parameters with the same spelling remain distinct.
A quantified callable is retained as a scheme, a contract that holds at every
allowed instantiation of its parameters. Lean checks its body under the
scheme's parameters and bounds, with its capture contracts, independently of
which concrete calls occur. Each call proposes an instance whose arguments
and bounds Lean checks.

[inference.ml](inference.ml) collects lower and upper constraints for one
call. A lower constraint requires a candidate to admit a type; an upper
constraint requires the candidate to fit within a type. Callback inputs
reverse the constraint direction; results preserve it.
Constraints also come from receivers, expected result types, construct
signatures, records, sequence shapes and applications of named declarations.
Dependent bounds propagate constraints between parameters. When generic
methods are compared, their local binders are renamed rather than treated as
parameters to solve for the enclosing call.

A union with exactly one bare inference variable selects an arm before
ordinary expansion of a named actual. This preserves the named type as a
candidate for the bare variable. For a native-promise arm containing type
variables, matching the native name or required field shape supplies candidate
constraints on those variables. A ground arm uses syntactic atom equality:
sharing a native constructor alone does not establish compatibility with its
fixed arguments. Thus `Promise<string>` against `Promise<number> | T` supplies
`T := Promise<string>`; against `Promise<U> | T`, native matching can instead
supply constraints on `U`.

Ground-arm selection performs no subtype comparison. It can miss a compatible
ground arm and propose a broader fallback variable. This is an incomplete
inference heuristic; Lean checks the resulting instance's bounds and full call
contract under the existing rules. The
[positive union cases](../pipeline/examples/generic-fixed-promise-union.ts)
exercise fixed, fallback and mixed arguments; the
[bounded negative](../pipeline/examples/invalid-generic-fixed-promise-union.ts)
requires rejection when neither the fixed arm nor the fallback's bound admits
the argument.

Candidate selection prefers the join of argument lower bounds. A named upper
bound supplies a candidate when no lower bound exists; other upper-only
candidates use representable intersections. Explicit literal bounds can retain
their literal alternatives during contextual widening. Declared bounds and
defaults remain part of candidate selection. An unconstrained
parameter without a usable candidate is proposed as `unknown`. Literal
candidates for an unbounded parameter can widen when the result does not return
that parameter directly: `box(42)` can infer `Box<number>`, while `id(42)` retains
`42`. A widened candidate stays below every upper bound, including those the
expected result places on a resolution-qualified parameter's observation or
result: an async `return "hello"` at `Promise<"hello">` retains `"hello"`.
A tuple arm of a bound can supply a contextual type for an array literal.
An object literal passed to a parameter bounded by a readonly dictionary
with no named members is inferred from its values with exact keys, including nested object literals.
Its declared bound is a separate read-view obligation; it supplies no storage
contract. Explicit annotations, named members and writable dictionary bounds retain
their contextual storage contracts.
These are inference choices; Lean checks the full instantiated contract.

Value types and argument packs have separate OCaml representations. A pack
specifies an argument list, including its arity; a rest parameter collects an
array at runtime. Substitutions distinguish value arguments from pack arguments
and refuse a lookup in the wrong role. A source binder used in both roles is
unsupported. Explicit call type arguments fix leading parameters before the
remaining ones are inferred.

The solver does not search every substitution or every overload alternative.
Structural decomposition and declaration unfolding have depth limits; a shape
it does not decompose contributes no guessed constraint. A deterministic
candidate can fail Lean validation even when another substitution would work.
Solver constraint records are local proposal state, absent from published
semantic types. The producer has no general existential-witness inference.

## Callable effects

Function types can propose that a call preserves its input heap: the contents
of heap locations existing when the call starts. Operand evaluation precedes
that guarantee. The producer
infers this property conservatively from bodies and carries it through supported
signature mappings, generic substitution and binding. An immutable annotated
binding can retain an inferred effect on the same callable signature; an
ordinary TypeScript annotation alone supplies no effect guarantee.

Lean certifies the effect together with the definition's typing before a call
can use it. Native array overloads can consume certified effects, for example
to establish an array result's presence. Preservation concerns normal return;
exceptional edges require their own state treatment. Composition has an
explicit admitted scope in the
[effect design](../docs/SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification)
and [effect typing rules](../docs/SOURCE-ELABORATION.md#definition-and-application-rules).

## Implementation map

| Module | Responsibility |
| --- | --- |
| [source.ml](source.ml) | Decode Fragment, annotations, declarations and scoped binders. |
| [flow.ml](flow.ml) | Decode statement graphs and solve states over their edges. |
| [execution.ml](execution.ml) | Decode expression and binding plans. |
| [semantic.ml](semantic.ml) | Immutable type, signature, field, sequence and pack representations. |
| [environment.ml](environment.ml) | Value snapshots, fixed cell contracts and current facts. |
| [inference.ml](inference.ml) | Call-local constraints, substitutions and candidate instances. |
| [type_queries.ml](type_queries.ml) | Read-only declaration expansion, member queries and construction hints, with explicit rigid bounds. |
| [proposal.ml](proposal.ml) | Coordinate function retries and module initialization, and assemble the program proposal. |
| [claims.ml](claims.ml) | Serialize candidates and intern clause rows. |
| [json.ml](json.ml) | Dependency-free JSON input and output. |
| [producer.ml](producer.ml) | Command-line proposal and explanation entry points. |

The proposal implementation separates these responsibilities:

- **Pass coordination and state:** [analysis_pass.ml](analysis_pass.ml) connects
  recursive expression, binding and body inference;
  [analysis_state.ml](analysis_state.ml) owns the state they share.
  [proposal_types.ml](proposal_types.ml) defines the candidate output records,
  and [proposal_diagnostics.ml](proposal_diagnostics.ml) owns observations and
  explanations for one run.
- **Execution:** [proposal_flow.ml](proposal_flow.ml) applies graph actions and
  manages path metadata and node outputs;
  [statement_analysis.ml](statement_analysis.ml) supplies statement transfers.
  [execution_analysis.ml](execution_analysis.ml) interprets expression schedules
  and obtains the environment at each observation;
  [binding_analysis.ml](binding_analysis.ml) interprets binding schedules.
  [refinement.ml](refinement.ml) supplies guard and field refinements.
- **Expression inference:** [expression_typing.ml](expression_typing.ml) chooses
  the source form and its entry environment. It delegates to
  [expression_values.ml](expression_values.ml),
  [expression_objects.ml](expression_objects.ml),
  [expression_properties.ml](expression_properties.ml),
  [expression_closures.ml](expression_closures.ml) and
  [expression_calls.ml](expression_calls.ml) for their corresponding forms.
  [expression_support.ml](expression_support.ml) supplies assignment-target contracts,
  constant assertions and failure explanations;
  [analysis_context.ml](analysis_context.ml) combines binding lookup, execution,
  closure offers and claim collection for those components.
- **Construction and publication:** [object_spread.ml](object_spread.ml) computes
  record alternatives for spreads; [closure_offers.ml](closure_offers.ml) gathers
  additional signatures requested by closure uses;
  [module_contract.ml](module_contract.ml) constructs the signatures visible to
  module callers. [claim_collection.ml](claim_collection.ml) records entries
  and instantiated member types through the publication interface.

Named recursive declarations retain their source identities. The producer can
inspect their equations for inference, while the claims refer to declaration
applications. Lean owns their interpretation. Likewise, array types,
intersections and scoped parameters use the protocol's label trees where Lean
constructs the corresponding rows. The claims document contains a table of
type rows. Numeric row labels identify entries in that table; they are separate
from rigid type-parameter identities.

Entry claims identify an execution point; expression claims identify that point
and a source span. The point includes the body's owner and local node identity.
This distinguishes repeated execution of one source expression, including
copies through `finally`, from distinct closure bodies. Conflicting claims at
one identity and missing required claims are validation failures.

## Reading and checking claims

The producer is unproved. Successful certification uses Lean's certificate
consumer and the theorem `SourceClaimJson.checkUnitJson_safe` for every accepted
function plan. That theorem concerns the modeled program. The parser,
source-to-model correspondence, native specifications, executable toolchain
and runner have separate trust obligations. The model's restrictions and
external-library assumptions are stated in [DESIGN](../docs/DESIGN.md) and
[program typing](../docs/PROGRAM-TYPING.md).

The admitted source language is a subset of TypeScript. Proposal limits include
unsupported mixed value/pack binders, certain spreads and pattern types,
ambiguous reused binding names in an input Fragment, and inference that does
not converge. The source parser handles ordinary lexical shadowing by renaming
bindings before proposal generation. Control-flow solving refuses
a node after 64 visits and begins forgetting refinements at repeatedly visited
joins after five visits. Evolving-contract inference runs up to four further
inference passes of a function after its first; a contract still growing then
is proposed from the binding's uses, and refused where no use fixes one. These limits can prevent a proposal for a safe program.
The [case inventory](../pipeline/cases.mts) states executable expectations.

## Extending the producer

Start with a motivating source and its negative control, registered in
[cases.mts](../pipeline/cases.mts). Candidate inference belongs in OCaml;
acceptance obligations belong in Lean. The
[agent rules](../AGENTS.md#iterating-run-what-the-change-touches) set the
checks to run, and [documentation ownership](../docs/DESIGN.md#documentation-map)
the document each fact belongs in.
