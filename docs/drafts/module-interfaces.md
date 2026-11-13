# Draft: module interfaces

## The existing mechanism this extends

[Certified imports](../SOURCE-CONTRACTS.md#certified-imports) give an
import the footprint established by its defining module's check.
[Stage replay](../STAGE-STORE.md#replay-and-trust) binds a completed
computation to its exact inputs and implementation. Both mechanisms are
listed in [general mechanisms](../DESIGN.md#general-mechanisms).
A component interface is the result of a process stage of that store.
Its per-module projections supply certified imports to the claims-free
front ([single pass](single-pass.md#9-the-claims-free-front)).

Mode 8 records the experimental pass's judgment. Its semantic guarantee
requires the single pass's planned soundness theorem; replay supplies only
the store's existing integrity and exact-input trust.

## Canonical computation

The own-file and imported paths use one component computation. It plans
each member module over its complete fragment, with every function as a
candidate, checks the groups needed to establish its proposed footprints,
and closes their dependencies. Written effects and inferred effects follow
the same publication rule. Measurement stand-ins are excluded from this
computation. Forced adversarial proposals are explicit request inputs.

An own-file publication supplies the parser's canonical `ModuleAst`, with
the imported path's location and declaration identities; an own-file
snapshot key is not a module identity. Given facts use
`module:<location>#<unit>` identities. An own-file request
normalizes its ordinary unit identities to these identities before invoking
the component stage. Conflicting lines for one identity are refused.
A selected importer run publishes no interface of its own: publication
requires the complete canonical component computation, even when only one
of its functions is requested.

## Components and dependency closure

The graph has a node for each implementation module in the fragment and
an edge for each resolved implementation import. Declaration-only imports
keep their existing contracts. Discovery starts at the selected importer's
resolved reads and closes over every candidate of each reached module.
Selection and measurement stand-ins choose the requested components; each
requested component retains its complete canonical inputs and checks. Strongly connected components form a DAG.
A component's members are ordered by module location; ready components are
ordered by their first location. These orders depend on the module graph,
independently of the requesting importer or selected function.

A component receives its member documents and the completed interfaces of
its outgoing dependencies. It checks members in canonical order, each
member one step that reads only the entries published before it, the
component's result the fold of those steps over its members. An import
of a later member has the ordinary effect; an earlier member contributes
only already established footprints. A group's successful check supplies
its dependency list. A footprint becomes established only when the group
and the transitive closure of its dependencies have successful checks.
Thus two conditional acceptances cannot bootstrap one another, within a
component or across cached stages. Module interfaces are projections of
one completed component result, published together.

## Interface contents and consumption

Each module projection binds its complete module document and records its
functions by name and name position. `established` records the footprint,
on-throw flag, returned footprint and defining group whose successful check
and dependency closure establish them, whatever proposed them, including a
written effect. `ordinary` means no stronger footprint is established.

A module with an established entry also carries its interface rows
(`rows`): the rows of its own store on the region its functions' interface
types reach (what each row reads, its meet's parts, its scheme's binders,
and the built-ins' types), numbered from `0`, with the built-ins
(`types`, `builtins`). Each established entry states its interface type as
positions in that table (`interface`): the type its function's callers
read it at in its module's store, lowered there at planning. The module
publishes an entry only where its function is in the module's laid-out
set (`FilePlans.laidOut`, the set $`D`$ of [the unit
theorem](pass-unit-theorem.md)'s module layout) and the store-map check
(`StoreMaps.matchStores`) from its store's interface type to the decoded
table's accepts, and the importer reads an entry only where the check from
the table's type to the type its own store reads the import at accepts,
each image operand a canonical union of the importer's store. A refused
read refuses each unit reading that import, at `signature rows differ`.
A store map relates the two stores' built-ins only where both state them,
so a module's document, and the document of a file importing one, list
`ArrayProto` whatever their code writes, and a store whose document lists
it states the built-ins (its arrays, their prototype and their `unknown`).
The two accepted checks give the importer's slot type the meaning of the
module's interface type (`signatureAgrees_of_checks`, proved on the
unit-level proof's branch), which the cross-module theorem reads, so the
rows are kept at their cost. Measured (2026-11-12, CPU best of 5
alternating runs at load 18–22, without and with the rows): the cases'
module stages 563 → 908 ms over 22 components, their interface documents
2.36 → 5.65 MB; pretext's `prepare` module stage 2,924 → 2,924 ms, its
importer 657 → 593 ms; `rich-inline`'s 5,270 → 4,987 ms, importer 1,282 →
1,226 ms. The check is incomplete for unions with two members of one row
shape, for qualified schemes, for two stores numbering a unique symbol
differently, and for a meet whose clause lists its fields in another order
(pretext's imports `missing` and `isCollapsibleSpaceCode`, refused at
`signature rows differ`).

The importer resolves a read using the existing declaration-identity,
eligibility and signature-agreement checks. It reads the matching module
projection only at the same document. The node adapter obtains projections
only from a successful stage invocation or a validated store replay.
An arbitrary JSON file is not authority for an established footprint.
The adapter and store are the replay trust boundary, as for existing
module-check results.

## Execution, keys and failures

The process manifest binds the stage, adapter implementation, verifier and
linked libraries, runner, runtime, argument vector, explicit environment,
exit protocol, output roles and the contents of every input file. The
component request binds its complete member documents, normalized given
facts, dependency interfaces and their stage keys, mode, depth, subtype
budget, forced proposals and `ALL_CUTS`. Dependency documents include their
source digests. Changes propagate through the component DAG.

The orchestrator resolves and executes dependencies **before acquiring the
parent's execution claim**. Shared work uses the store's existing claims,
publication, integrity checks, timeout observations and resource budgets.
There is no evidence reuse. A timeout, missing input or operational failure
publishes no interface. A completed semantic refusal can produce ordinary
entries. An importer's temporary fallback to ordinary effects is local to
that invocation and is never stored under the successful component key.
Wire decoders require every field and refuse unknown fields; there is no
version tag.

## Entry points

`--module-interface-plan <fragment> <selection>` discovers the requested
canonical component DAG. The selection supplies function names, stand-in
names, and explicit own-module roots. Both input files bind the stage key.
`--module-interface <request>` prints one component's closed interfaces.
Both commands are process stages through `verifierCall` and `invokeProcess`.
`prepareInterfaces` resolves them dependency first. Its `ownModule` input
is the parser's canonical module document for an own-file publication.

`verifyWithInterfaces` first checks the importer at ordinary import contracts.
A successful check needs no stronger module facts and returns that check's
verdicts, with their dependencies. It publishes no module interface. A semantic
refusal requests the reachable components and checks the importer with their
projections. Operational failures propagate. Explicit own-module publication
and forced-proposal controls run the complete requested component checks.
An empty established set requires no module resolution in importer planning.
Its `--verify-interface-stage` command suppresses measurements for stable
stage payloads; `--verify-interfaces` runs the identical check with the
measurement output available. The direct `--verify-units 8|9` command uses
`establishModules` in the same invocation when no store adapter is present;
it publishes nothing. The canonical computation is shared; the predecessor's
demand-dependent module walks and least-effect pruning are removed.

## Measurements

The predecessor's measurements (2026-11-11, mode 8, gate stand-ins, best
CPU of three) are 1275 ms for `measureAnalysis`, 5794–7146 ms for
`prepareRichInline`, and 142 ms for `buildEngineProfile`. The corresponding
f894d34a measurements in that session are 934, 2188 and 143 ms.
Warm importer cost near those earlier numbers is a conjecture: established
footprints affect the importer's own work. Cold cost includes discovery,
complete component checks, process startup, serialization and publication.
The required measurements are cold total CPU and wall time, warm importer
CPU, concurrent runs sharing a dependency, and equality of the footprints
read with those established by a8dadf7f. A census or case runner's ordering
does not establish that dependencies are already cached.
