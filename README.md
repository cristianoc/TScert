<p align="center"><img src="assets/logo.svg" width="128" alt="TScert logo"></p>

# TScert: independent claim verification

This pipeline checks type claims about TypeScript programs. A **claim** is a
proposed expression type or a description of local variables at a program
point. The OCaml producer proposes those claims; Lean checks whether they
follow from the program and its declared inputs.

Lean first turns source syntax into execution plans describing control flow,
operand order and variable binding. OCaml computes type facts over those plans.
Lean then reconstructs the plans, uses the proposed types to elaborate a
**calculus graph**—a program in the verifier's formal language—and checks
certificates for its typing obligations. A certificate records a derivation
that the checker can validate. Neither type inference nor evidence search is
trusted to produce correct answers.

There is one maintained calculus and verifier. Its implementation lives in
`lean/Verification/`, organized by semantics, types, program rules,
source integration, and tests. Declarations live under the `Verification`
namespace; module paths identify their topic. These folders aid navigation,
not an enforced dependency order: some derived semantic lemmas depend on
program rules.
[DESIGN.md](DESIGN.md) describes the architecture and trust surface;
[REFERENCES.md](REFERENCES.md) collects the works it draws on.

Start with [the architecture](DESIGN.md#architecture) for the full data flow
and [the language map](LANGUAGES.md) for the representations exchanged between
components. The formal definitions live in [SEMANTICS](SEMANTICS.md), which
defines execution and safety, [POSITIVE-TYPES](POSITIVE-TYPES.md), which defines
types and state assertions, and [PROGRAM-TYPING](PROGRAM-TYPING.md), which
defines the rules used to check programs.

The TypeScript the pipeline reads is summarised under
[current source fragment](#current-source-fragment); the
[fragment boundary](SOURCE-FRAGMENT.md#fragment-boundary) lists what it refuses and why.

## Run

Prerequisites: Node, the pinned [Lean toolchain](lean/lean-toolchain), OCaml
and Dune ([the producer guide](ocaml-producer/README.md#try-it)). Install the
tools once:

```sh
make setup
make test
make suite
```

[tools/package.json](tools/package.json) pins what the node side installs: the
TypeScript compiler the parser runs on, and KaTeX, which
checks the documents' math. [lean/lakefile.toml](lean/lakefile.toml) declares
the Lean package Lake builds: the `Verification` library and the `verifier`
executable. [.gitignore](.gitignore) keeps what these commands write, Lake's
build and manifest and npm's lock, out of the repository.

Tests favour end-to-end pipeline cases, source files through the parser, the
OCaml producer and Lean, over unit tests of intermediate steps; tests written
while researching a feature retire once a pipeline case covers it
([AGENTS.md](AGENTS.md#which-tests-to-keep)).

- `make test` runs the fast checks, in seconds, with nothing built
  ([test-all.sh](test-all.sh) starts them together and reports them in order):
  front-end types, JSON field names, assertions with their reasons, documents,
  examples run under Node, the trusted inputs and the rule inventory. Its
  summary counts test executables, not functions or assertions, and marks an
  incomplete run after an early failure.
- `make suite` builds Lean and the producer (`make build`), then runs every
  pipeline case and the forged documents and claims no case can make
  ([pipeline/test.mts](pipeline/test.mts)), showing how many cases have
  finished.
- `make cases P=…` runs the pipeline cases whose file names contain `P`;
  `make check FILE=…` runs one source file through the pipeline. `make help`
  lists every target.

Terminal output uses green for success, red for rejection or failed proof search,
and amber for unavailable checks. Symbols and words remain visible without
color. Redirected output, `TERM=dumb`, and a nonempty `NO_COLOR` disable
colors.

## Current source fragment

The *fragment* is the subset of TypeScript the verifier accepts; a *Fragment*
document is the parser's tree of one source in it
([LANGUAGES](LANGUAGES.md#the-languages)).

A source file is a module, checked per code unit: each function, and the
module's initialization, which runs its constants, classes, enums and
top-level statements ([modules and code units](DESIGN.md#modules-and-code-units)).
In outline, the parser admits:

- **Statements**: `const` and `let` bindings, annotated or not (a `let`
  nothing writes is a `const`); object and array patterns with defaults,
  holes and rests; `if`, `switch`, `while`, `for`, `for...of` over arrays,
  `for...in`, labeled blocks, `break` and `continue`; `throw` and
  `try`/`catch`/`finally`, a throw being an outcome
  ([statement forms](SOURCE-CONTRACTS.md#statement-forms),
  [patterns](SOURCE-ELABORATION.md#patterns), [throws](SOURCE-MODEL.md#throws)).
- **Values and operators**: `null`, `undefined`, Booleans, numbers, bigints,
  strings and symbols, with literal types; arithmetic, relational comparison
  of operands in their primitive order, string `+` and template literals,
  compound and logical assignment; `typeof`, `in`, `instanceof`,
  truthiness, strict equality, and supported loose-equality comparisons
  ([values](SOURCE-MODEL.md#values), [guards](SOURCE-MODEL.md#guards)).
- **Objects and arrays**: object literals with spreads, records, index
  signatures, dense arrays and tuples, optional chaining, enums, and classes
  with fields, methods, statics, parameter properties and a base class of the
  file ([objects and prototypes](SOURCE-MODEL.md#objects-and-prototypes),
  [classes](SOURCE-CONTRACTS.md#classes)).
- **Functions**: declarations, function expressions and arrows with
  optional, default and rest parameters, closures as graph code, methods whose contracts depend on their receiver, `.call`, `.apply` and `.bind`; generic functions and
  classes certified at every instantiation; `async` functions and `await`
  of promises of primitives ([calls](SOURCE-MODEL.md#calls),
  [generic bodies](DESIGN.md#generic-bodies),
  [async and iteration](SOURCE-MODEL.md#async-and-iteration)).
- **Types**: what TypeScript's declarations state, read by the declaration
  reader: aliases, interfaces, unions, intersections, computed types and
  library types through reviewed overlays; imports, ambient declarations and
  globals are assumptions at their declared types
  ([trust surface](DESIGN.md#trust-surface)).

A type assertion (`e as T`, `e satisfies T`, `e!`) decides nothing: `T` is one
more type the operand must meet, so an assertion never establishes what a
guard would.

Unsupported forms are refused with a reason. Where source locations are
available, diagnostics identify the relevant span. The fragment is smaller
than the calculus, and the parser can represent syntax the Lean adapter then
rejects: such a rejection is a limitation, never evidence that a producer
claim is false.

[The fragment boundary](SOURCE-FRAGMENT.md) owns what is refused and why.
[Source contracts](SOURCE-CONTRACTS.md) explains how declarations are read;
[Fragment](FRAGMENT.md) owns the syntax encoding, and
[the request protocol](REQUEST-PROTOCOL.md) owns the verifier commands and
calculus request/evidence encoding. Worked examples of each construct are the
[pipeline cases](tests/README.md), including the
[callable examples](pipeline/examples/callables/README.md); the
[callable surface](pipeline/examples/callables/README.md#the-callable-surface)
states which TypeScript callable forms are supported and where each
unsupported one stops.

## What is established

1. The front end uses TypeScript’s compiler API to produce source syntax and declarations.
2. Lean constructs execution plans; OCaml proposes types and environments over them.
3. Lean reconstructs those plans and elaborates a calculus request, retaining
   source annotation obligations.
4. Proof search proposes evidence; certificate checking validates it against
   that exact request. Acceptance implies typing and modeled execution safety.

Termination is not guaranteed. Applying the safety result to JavaScript still
requires trust in source parsing, extraction, the semantic definitions and Lean's
execution infrastructure. Source extraction is reviewed, not proved equivalent
to JavaScript. Accepted functions do not certify every unused displayed claim.

## Documentation ownership

Each document owns one layer. Keep definitions and detailed examples in that
owner; other documents link to them and give only the context their readers need.

| Document | Owns |
| --- | --- |
| This README | Commands, a concise supported-fragment overview, and navigation. |
| [DESIGN](DESIGN.md) | Principles, architecture, trust surface and lasting decisions. |
| [SOURCE-MODEL](SOURCE-MODEL.md) | How source values and operations map to the calculus and its host assumptions. |
| [SOURCE-FRAGMENT](SOURCE-FRAGMENT.md) | Enforced source restrictions and translation limits. |
| [WORK](WORK.md) | Open work, its reasons and completion conditions. |
| [SEMANTICS](SEMANTICS.md) | The term and value grammar, execution, worlds, heap satisfaction, membership and safety predicates. |
| [POSITIVE-TYPES](POSITIVE-TYPES.md) | Types as positive formulas (clauses under union and intersection, no negation): type and state-assertion grammars, normalization, declarative subtyping and subtype certificates. |
| [RECURSIVE-EQUATIONS](RECURSIVE-EQUATIONS.md) | Generic declarations as parameterized equations: labels, unfolding, substitution, family subtyping, lowering, wire format and acceptance statement. |
| [PROGRAM-TYPING](PROGRAM-TYPING.md) | Core expression, graph and state typing rules, their side conditions and soundness scope. |
| [SOURCE-ELABORATION](SOURCE-ELABORATION.md) | Evidence search and source compilation obligations, including bindings, closures and parameter initialization. |
| [SOURCE-CONTRACTS](SOURCE-CONTRACTS.md) | Source declarations, library contracts and the interpretation of annotations. |
| [CALLABLES](CALLABLES.md) | The proved callable fragment and the proposed broader callable rules, with their distinct proof scopes. |
| [REQUEST-PROTOCOL](REQUEST-PROTOCOL.md) | Request/evidence JSON and the verifier CLI. |
| [FRAGMENT](FRAGMENT.md) | Source syntax wire format and its relation to execution plans and claims. |
| [SOURCE-CLAIMS](SOURCE-CLAIMS.md) | The independent claims document schemas and source identity. |
| [LANGUAGES](LANGUAGES.md) | Every representation data crosses, which file owns each on both sides, the naming convention, and where it does not hold. |
| [OBLIGATION-DIAGNOSTICS](OBLIGATION-DIAGNOSTICS.md) | Failure records, source maps, outcome classification and reason vocabulary. |
| [CLAIM-LANGUAGE](CLAIM-LANGUAGE.md) | The claim text language diagnostics print: its two typed representations. |
| [Test index](tests/README.md) and the [callable examples](pipeline/examples/callables/README.md) | Regression coverage, the pipeline cases and their runnable witnesses. |
| [REFERENCES](REFERENCES.md) | Every cited paper, specification, tool and issue, with what the project uses from it and where. Other documents link to its anchors. |
| [TRUST-REDUCTION](TRUST-REDUCTION.md) | The bridges between source and theorem that rest on review, the options for narrowing or proving each, and host lemmas against a mechanized ECMA-262. |

When adding a rule, put its mathematical statement and proof scope in
`PROGRAM-TYPING` (or `POSITIVE-TYPES` for subtyping). New semantic predicates go
in `SEMANTICS`; wire fields go in the relevant protocol document. Record architecture decisions in `DESIGN` and remaining integration in `WORK`.
Keep case mechanics with the cases. Distinguish **exportable**, **proved in
the model**, and **accepted by the source checker** wherever those statuses differ.
Avoid temporary paths, task handoffs and duplicate field tables in maintained
docs. Lean definitions and tests remain the implementation evidence; cite them.

What a change must carry depends on the layer it touches. A new typing or
subtyping rule needs its soundness lemma in the model and a `#print axioms`
line. A new lowering or adapter case needs no lemma, but it must emit its
checks as located obligations (never a bare string), reuse an existing rule
rather than add an approximate one, and come with a positive witness, an
independent negative control and a tampering test; see the
[test index](tests/README.md). A new wire field needs its decoder, every
producer and consumer updated together, and a tampering test for the field.
A compilation of one form into existing rules needs a statement of what
justifies it — the compiled derivations are consequences, never the reason for
acceptance — and one interface so a later certificate can replace it.

The source boundary starts in
[Fragment.lean](lean/Verification/Source/Fragment.lean) and
[SourceExtraction.lean](lean/Verification/Source/SourceExtraction.lean).
[SourceFacts.lean](lean/Verification/Source/SourceFacts.lean) supplies assignment
and ownership analyses; [SourceRequests.lean](lean/Verification/Source/SourceRequests.lean)
checks source interfaces and obligations using the graph evidence that
[RequestJson.lean](lean/Verification/Source/RequestJson.lean) validates.

Typed lowering is organized around three recursive operations: compiling an
expression, a binding schedule, or a statement body.
[SourceExtraction.lean](lean/Verification/Source/SourceExtraction.lean) connects
them through [explicit callbacks](lean/Verification/Source/LoweringCallbacks.lean)
and constructs each function request. Separate modules handle
[closure code](lean/Verification/Source/LoweringClosures.lean),
[expression proofs](lean/Verification/Source/LoweringExpression.lean),
[atomic operations](lean/Verification/Source/LoweringAtoms.lean),
[operand schedules](lean/Verification/Source/LoweringExecution.lean),
[bindings](lean/Verification/Source/LoweringBindings.lean), and
[control flow](lean/Verification/Source/LoweringFlow.lean).
[Construction state](lean/Verification/Source/LoweringState.lean) is private to
its owner. Lowering components compose an abstract `Compiler` through operations
for graph construction, observations, obligations and code publication. Temporary
execution bindings, receivers, handlers and graph frames have scoped operations.
The extraction runner returns an immutable result containing the completed
graph and shared outputs. The type boundary excludes general state access and
raw compiler-state replacement from consumers.

The source-claims boundary has a [wire decoder](lean/Verification/Source/SourceClaimWire.lean),
[scheme interpretation](lean/Verification/Source/SourceClaimSchemes.lean),
[source-site validation](lean/Verification/Source/SourceClaimSites.lean), and
[equation preparation](lean/Verification/Source/SourceClaimPreparation.lean).
[Request extraction](lean/Verification/Source/SourceClaimExtraction.lean) combines
them with typed lowering. [Plan certification](lean/Verification/Source/SourceClaimPlans.lean)
requires every extracted plan to cross an exhaustive conversion before
[the acceptance entry point](lean/Verification/Source/SourceClaimJson.lean)
checks evidence. That entry point also owns the theorem connecting its exact
success condition to safety of every accepted function.

[Equation lowering](lean/Verification/Source/EquationLowering.lean) turns
source declarations, annotations and claim labels into recursive equations.
Its [core](lean/Verification/Source/EquationCore.lean) handles mutually recursive
type constructors and declaration references; separate modules own
[declaration decoding](lean/Verification/Source/EquationDeclarations.lean),
[claim-row decoding](lean/Verification/Source/EquationClaimWire.lean),
[annotation traversal](lean/Verification/Source/EquationAnnotations.lean),
[instance matching](lean/Verification/Source/EquationInstances.lean), and
[final validation](lean/Verification/Source/EquationFinishing.lean).
[Construction state](lean/Verification/Source/EquationState.lean) carries pending
rows and bound obligations through those stages.

The main Lean entry points are:

| Area | Entry points |
| --- | --- |
| Operational semantics and worlds | [Calculus](lean/Verification/Semantics/Calculus.lean), [Worlds](lean/Verification/Semantics/Worlds.lean), [ObjectCoherence](lean/Verification/Semantics/ObjectCoherence.lean) |
| Semantic families and graph types | [Types](lean/Verification/Types/Types.lean), [PositiveGraphs](lean/Verification/Types/PositiveGraphs.lean), [PositiveRules](lean/Verification/Types/PositiveRules.lean) |
| Program typing and checked evidence | [ProgramTyping](lean/Verification/Programs/ProgramTyping.lean), [ProgramCertificates](lean/Verification/Programs/ProgramCertificates.lean), [CertificateProducer](lean/Verification/Programs/CertificateProducer.lean) |
| Source boundary and CLI | [Fragment](lean/Verification/Source/Fragment.lean), [SourceExtraction](lean/Verification/Source/SourceExtraction.lean), [SourceClaimJson](lean/Verification/Source/SourceClaimJson.lean), [RequestCli](lean/Verification/Source/RequestCli.lean) |
| Other code and tests | [OCaml producer](ocaml-producer/README.md), [Node tools](tools/), [regression index](tests/README.md) |

Claims documents preserve current-content assertions such as
`{ value: boolean = (true) }`, separately from the storage invariant. Supplied
observations are checked obligations: every incoming edge, including loop
backedges, must establish the assertions claimed at a statement entry. See
[Current-content assertions](SOURCE-MODEL.md#current-content-assertions).
