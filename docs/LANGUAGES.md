# The pipeline's languages

The pipeline exchanges several representations of the same source program.
This guide identifies what each representation describes and where its syntax
is defined. [The architecture](DESIGN.md#architecture) explains their order in
the pipeline; the linked protocol documents define their encodings.

A **source span** identifies syntax by offsets in the source file. An
**execution point** identifies a statement-graph node; one source span can
belong to several points. A **type label** names an entry or expression in a
type graph. A **certificate** records a proposed derivation for the checker to
validate. These identities and roles are distinct even when they use integers
on the wire.

## The convention

Each language has an identified owner on each side of an interface. A schema
file defines the representation; a consumer file names its role, such as
`fragment-parse` or `diagnostic-view`. Matching Lean and TypeScript schema files
use `PascalCase.lean` and `kebab-case.mts` where their responsibilities align.
The exceptions below explain shared and split definitions.

Exhaustive pattern matches help expose unhandled constructors. TypeScript case
tables keyed by a union, such as `Record<Tag, true>`, similarly expose missing
keys. These checks do not enforce file ownership or semantic agreement between
languages.

## The languages

| Language | Lean definition or codec | Other definitions and readers | Produced by |
| --- | --- | --- | --- |
| **Fragment** — the subset of TypeScript this pipeline accepts, as a tree; its required `declarations` slot is emptied once Lean has interpreted its equations | [Fragment.lean](../lean/Verification/Source/Fragment.lean) | [fragment.mts](../tools/fragment.mts), parsed by [fragment-parse.mts](../tools/fragment-parse.mts) | the parser |
| **Declaration graph** — the source type equations of every local and imported declaration a file reaches, with the declaration TypeScript binds each name to; function annotations are written in the same source type terms | [Equations/Lowering.lean](../lean/Verification/Source/Equations/Lowering.lean) | [declaration-types.mts](../tools/declaration-types.mts), read by [type-term.mts](../tools/type-term.mts) and collected by [declaration-graph.mts](../tools/declaration-graph.mts) | the parser, with TypeScript's checker |
| **Claim expressions** — structural type expressions used by diagnostics and internal source-type conversion | [Claim.lean](../lean/Verification/Types/Claim.lean) | [claim.mts](../tools/claim.mts), printed by [claim-text.mts](../tools/claim-text.mts) | claim parsing and type conversion |
| **Source execution plans** — claim-independent control-flow graphs with expression and binding schedules | [FlowJson.lean](../lean/Verification/Source/FlowJson.lean) writes [FlowGraph.lean](../lean/Verification/Source/FlowGraph.lean), [ExpressionPlan.lean](../lean/Verification/Source/ExpressionPlan.lean) and [BindingPlan.lean](../lean/Verification/Source/BindingPlan.lean); [ExecutionRoots.lean](../lean/Verification/Source/ExecutionRoots.lean) selects each node's expressions | [source-flow.mts](../tools/source-flow.mts); OCaml readers flow.ml and execution.ml | Lean source lowering |
| **Resolution metadata** — a qualified type parameter's owned names (`resolution` in the Fragment's `typeParams`) | [ResolutionWire.lean](../lean/Verification/Source/ResolutionWire.lean) | [declaration-types.mts](../tools/declaration-types.mts) (`ResolutionSlots`) | the parser |
| **Calculus** — terms, tags, call codes: the operational language | [Calculus.lean](../lean/Verification/Semantics/Calculus.lean) | [calculus.mts](../tools/calculus.mts) | extraction |
| **ControlFlow** — the program graph over those terms | [ControlFlow.lean](../lean/Verification/Programs/ControlFlow.lean) | [control-flow.mts](../tools/control-flow.mts) | extraction |
| **TypeGraph** — positive types as labelled rows | [PositiveNormalization.lean](../lean/Verification/Types/PositiveNormalization.lean) | [type-graph.mts](../tools/type-graph.mts) | extraction |
| **Request** — the whole verification request | [RequestJson.lean](../lean/Verification/Source/RequestJson.lean) | — | extraction |
| **Evidence** — certificates the checker validates, written as tables with backward references | [ProgramCertificates.lean](../lean/Verification/Programs/ProgramCertificates.lean), [PositiveCertificates.lean](../lean/Verification/Types/PositiveCertificates.lean); the document, EvidenceWire.lean | — | proof search |
| **Diagnostic** — why an attempt did not succeed | in [RequestJson.lean](../lean/Verification/Source/RequestJson.lean) | [diagnostic.mts](../tools/diagnostic.mts), rendered by [diagnostic-view.mts](../tools/diagnostic-view.mts) | the verifier |

A representation's syntax does not establish the truth of what it says.
Fragment and declaration collection are trusted translations of source. Source
execution plans guide proposal generation; Lean reconstructs them for checking.
SourceClaims contains untrusted type proposals. Request contains the extracted
program and obligations; Evidence proposes derivations for that exact request.
Diagnostic explains an outcome and has no role in acceptance.

The OCaml producer has internal inference types and environments as well as
these external documents. Those internal data structures are not additional
protocols. The producer guide explains their roles.

Exact callable fields and effect contracts belong to the
[request protocol](REQUEST-PROTOCOL.md), declaration terms to
[recursive equations](RECURSIVE-EQUATIONS.md), and claim identities and type
labels to [source claims](SOURCE-CLAIMS.md). A wire change requires checking
all writers and readers, including the preservation of meanings such as
readonly storage, array presence and callback effects.

## Where the rule does not hold, and why

- **Source execution plans** combine three Lean languages in one wire document.
  `FlowJson.lean` serializes their constructors; `source-flow.mts` validates the
  combined wire, while OCaml separates graph and expression/binding decoding.
- **TypeGraph** has no single Lean counterpart. `Clause` lives in
  `PositiveNormalization.lean` because the clause meet and its proof
  (`meet_sound`) are stated over it, and moving it to buy a matching filename would separate a definition from
  the theorems about it. The mirror is named for the language; the Lean side is
  named for the proof.
- **Request** and **Evidence** are interpreted by Lean for acceptance. Tests
  and the diagnostic tools inspect selected fields, but do not provide a second
  acceptance checker or a complete TypeScript schema.
- **A call signature's effect** has one JSON form inside three documents,
  the declaration document, the claims and the evidence. One Lean file reads
  and writes it, [EffectJson.lean](../lean/Verification/Source/EffectJson.lean),
  re-encoding what it read so that any other field is refused; `CallEffect`
  in [declaration-types.mts](../tools/declaration-types.mts) declares it for
  TypeScript, [type-graph.mts](../tools/type-graph.mts) decodes it, and the
  producer reads and writes it in `source.ml` and `claims.ml`.
- **span.mts** mirrors only half of `Decode.lean`. TypeScript has no shared JSON
  accessors, because each language file validates its own shapes.

## Known gaps

Exhaustive decoders cannot force a producer to emit every supported construct.
A missing inference case can cause an unsupported result even when the verifier
could check a suitable proposal. Likewise, field-name agreement does not prove
agreement on evaluation order or effects. Coverage measurements, forged-document
controls and execution witnesses provide evidence for these separate properties.

## Adding a language

Identify its semantic role and schema owner, add it to the table, and document
its producers and consumers. Give every variant an exhaustive decoding path.
Declare the cross-language agreement that its implementations must maintain,
including consumers whose behavior can violate that agreement. Keep exact wire
fields in the protocol owner and link to them from this catalogue.
