# The stage store

Every stage the pipeline's entry point runs, imported modules and repeated
proposal and search attempts included, and every operation a control runs,
goes through one invocation mechanism ([`pipeline/stages.mts`](../pipeline/stages.mts))
and one content-addressed store. Each invocation has an explicit input
description, immutable inputs and a recorded result, and replays a stored
result where its key matches. [DESIGN](DESIGN.md#the-stage-store) gives the
summary and the [trust surface](DESIGN.md#trust-surface) the rows replay
adds; this document owns the mechanism.

## Keys

A key is the SHA-256 of a canonical encoding of the stage,
its implementation and its complete input description. Ordering is retained
where it affects execution. The implementation includes the stage's
execution adapter, the code the stage runs and the runtime it runs on.
A package version or executable pathname alone does not identify it.

Code identity uses whole-directory enumeration, complete by construction
within the declared universe: the direct-child `.mts` files of `pipeline/`
and `tools/`, with the exclusions below. It involves no import discovery.
`tests/` and `dev/` are outside this universe. A key covers:

- for a process stage, the digest, by sorted path and content, of every
  `.mts` file directly in `pipeline/` but those excluded below, with the
  executable and its libraries, the stage runner and its libraries
  ([timing](#timing)) and the Node runtime;
- for an in-process stage, the same digest over every `.mts` file directly in
  `pipeline/` and in `tools/` but those excluded below, with the Node runtime
  and, for an observed stage, the compiler's packages and the system's
  build.

An executable's libraries are those its platform's loader loads, each by
its digest: on macOS the libraries its Mach-O load commands name,
transitively, resolved as dyld resolves them, a library of the sealed system
volume by the system's build instead; on Linux the program interpreter its
ELF header names and every library that interpreter lists for it
(`ld.so --list`). A process whose environment, or whose stage child's,
holds a `DYLD_` or `LD_` variable, and on Linux a system with a preload list
(`/etc/ld.so.preload`), have no key: those load code the identity does not
name. Other platforms have no key.

A file within the universe is keyed by default: a new or renamed keyed
module changes every key it falls under. The exclusions are the lists
`unkeyed` and `inProcessOnly` of `pipeline/stage-execution.mts`, which the
code owns. Each names a file whose role is to choose among entries whose
stored manifest equals the invocation's own, to publish or record attempts,
to orchestrate stages over inputs the manifest binds, or to present
outcomes; none computes a stage's result from its inputs. A file joins the
list with its role stated here, in the same commit.

Excluded from every key (`unkeyed`), by role:

- `pipeline/stages.mts`: the replay policy (forcing, finished and timeout
  lookup, retrying timeouts, publication calls) and the attempt records;
- `pipeline/stage-store.mts`: the store's lookup, validation, publication and
  cleanup;
- `pipeline/verify-source.mts`: the orchestration of one check, passing
  values to the stages' calls, and its outcome;
- `pipeline/unit-slices.mts` and `pipeline/unit-documents.mts`: a
  document's units of proposal and each unit's slice, inputs of the stages
  that read them ([units of a proposal](#units-of-a-check)), and the
  documents' types;
- `pipeline/run-cases.mts`, `pipeline/cases.mts`: the case runner and the
  case inventory;
- `pipeline/test.mts`, `pipeline/default-parameters.mts`,
  `pipeline/evidence-mutations.mts`, `pipeline/generic-rest.mts`,
  `pipeline/overload-claims.mts`, `pipeline/rest-pack-instance.mts`: the
  controls and their forged inputs, which reach a stage only as manifest
  inputs;
- `pipeline/run-example.mts`, `pipeline/fixture-links.mts`: running an
  example under Node, and creating the fixture projects' links;
- `tools/diagnostic.mts`, `tools/diagnostic-view.mts`, `tools/claim-text.mts`:
  decoding and rendering diagnostics after the stages;
- `tools/unchecked.mts`, `tools/shadow-contracts.mts`, `tools/child-output.mts`:
  the `any` audit of the node side's sources, a suite, and the child
  processes it runs its parts in;
- `tools/strip-types.mts`: type erasure for the examples run under Node by
  the excluded controls;
- `tools/compiler-processes.mts`: the attempt records' measurement of the
  compiler processes' CPU time and peak memory.

Excluded from process keys, beside those: the in-process stages' own
modules (`inProcessOnly`), `pipeline/parse-stage.mts`, `pipeline/claims-assembly.mts` and
`pipeline/in-process-execution.mts`, and every module of `tools/`, the front
end, which a process stage's binding and run in `pipeline/stage-execution.mts`
do not execute.

*Completeness.* Result-path completeness rests on three audited assumptions:
excluded files contribute no result-affecting code; process-stage binding,
execution, classification and materialization execute no in-process stage
or `tools/` code; and result-affecting repository code is confined to the
direct-child `.mts` files of `pipeline/` and `tools/`. External code is
limited to identified executables and their libraries, Node built-ins
covered by the runtime identity, the observed stage's compiler packages
covered by compiler identity, and family loads covered by the loader's
observations. Identified executables and observed family loads are exceptions
to the repository-code and process-stage restrictions. Loading code outside
this universe is an audited assumption, not a mechanically refused action.

The identity is captured when the process loads its modules: the sorted
file set and every file's digest. Failed enumeration or an unreadable file
leaves the invocation without a key. At stage entry and before publication,
the file set and every file's content must match the captured identity;
a difference makes the invocation execute without a key and publish
nothing.

That every result-affecting file-system read passes through the observation
mechanism (`tools/files.mts`), including reads reached indirectly
(`process.getBuiltinModule`) or by evaluated code, is a separate audited
assumption of observed stages. The fast check `tests/observed-stages.mts
--reads` checks the listed import forms toward it; it parses every keyed
module of the in-process universe with the TypeScript compiler's own parser,
through the compiler API the front end opens, over `tools/tsconfig.json`.
It refuses import declarations, export-from declarations and `import(…)`
calls whose specifier names a Node file-system, module, process, worker or
vm module, and every `import(…)` whose argument is not a string literal.
The exceptions are `tools/files.mts`, `pipeline/stage-execution.mts` and
`pipeline/run-directory.mts`: the execution adapters read the code they
identify and a process stage's inputs, never an observed stage's inputs;
and `tools/module-hooks.mts`, which runs Node's resolution and loading for
`tools/files.mts`, its one importer (the check refuses another, by an
import declaration, an export-from declaration or `import(…)`), which
observes what each read.

*Cost.* An edit of any keyed file misses every entry of the kinds it keys:
an edit of a front-end module misses every parse, diagnostics and assembly
entry, and an edit of a keyed pipeline module every entry. An edit of an
excluded file replays everything.

Each in-process stage's call is constructed by its own module: the input
description, execution over exactly those inputs, codec and, for an
observed stage, compiler identity. `pipeline/parse-stage.mts` owns the parse
and TypeScript diagnostics calls; `pipeline/claims-assembly.mts` owns
assembly. The orchestration passes values only.

Replay policy (`pipeline/stages.mts`), store lookup, validation and
publication (`pipeline/stage-store.mts`), and outcome presentation are outside
keys. Presentation includes attempt records and their decoders, orchestration
and diagnostic formatting. Replay validation, including `storedObservations`,
`observationsHold` and stored-input comparison, preserves exact manifest
equality and observation validity. Excluding policy and store code assumes
that every publishing and reading version binds results to their exact
manifests: a replayed result is exactly what execution on the key's inputs
produced. Repair of a publication or reading defect includes invalidation of
entries it could have written (`make clean-store`).

## Inputs and replay eligibility

Each invocation fixes or records its arguments, working directory,
observable environment and runtime options. Executable dependencies and
in-process configuration are inputs too. An invocation whose dependencies
cannot be identified executes without replay. An executable's identity is
computed once and kept while every file it was computed from has the
status (device, inode, size, modification and change times) observed before
it was read; a file whose status changes while the identity is computed has
it computed again (`heldIdentity`, `pipeline/stage-execution.mts`).

All stages use the common invocation mechanism. Replay requires complete
dependency identification, consistent compiler state where applicable,
established path equivalence and audited result binding. An invocation
failing these requirements executes without replay and retains its timing
and outcome records. Every stage in the table replays; the parse and
TypeScript's diagnostics where their observations are complete
([observed stages](#observed-stages)).

An invocation whose dependencies cannot be identified has an attempt
identity and a record of its known inputs, but no reusable stage key. Its
result and timeout observations are retained only as attempt records;
neither is published or reused as a stage entry. The stage-key publication
and timeout-reuse rules apply only to replay-eligible invocations. Force
execution of a replay-eligible invocation retains its complete stage key.

| Stage | Inputs in addition to its implementation and execution context |
| --- | --- |
| parse | source bytes and logical identity; project and resolution context; active host-family descriptions; the functions read at their declared signatures (`omitted`); the complete filesystem observations of parsing, declaration collection and host activation, its imported modules' stages' included |
| module | an imported module's path and identity in the importer's documents; the project; active host-family descriptions; whether the run gives a tag selection; its observations, its reads of the selection by family among them ([shared work](#shared-work)) |
| lower | the exact Fragment document, or a unit's slice |
| facts | the exact Fragment ([units of a proposal](#units-of-a-check)) |
| propose | a unit's slice, its flow and its reads document ([units of a proposal](#units-of-a-check)) |
| assemble | the units' proposals, each with the intervals its slice leaves out; the Fragment with its own declarations named canonically; the qualified-read document |
| assemble claims | the assembled proposal and ordered transitive module-claim documents selected by the reads |
| plan | the exact Fragment and assembled claims |
| module search | the exact module run the plan printed: an imported module's document restricted to the read closure of the functions read qualified of it, its claims and its own qualified reads; search depth and subtype rounds |
| module check | the same module run and its evidence; subtype rounds |
| search | a unit's slice, its claims and the qualified reads it is searched at; search depth and subtype rounds; the unit's members |
| check | the exact Fragment, assembled claims and the units' evidence, each slice's line with its store's heads; explicit file identity; source snapshot binding; subtype rounds; the selected units |
| explain | a unit's slice, its flow and its reads document, the imports read at their ordinary signatures |
| TypeScript diagnostics | source identity, project context and the complete compiler dependency observations |

## Units of a check

A document, the checked file's or an imported module's, is proposed a unit
at a time, and the checked file's units are searched a unit at a time, so an
edit of one function proposes and searches again only the units whose
inputs it changes. The check reads the whole document.

- *Units.* `producer --units` reads the whole document and prints, for each
  function name, the module functions its code mentions, whether it
  mentions a name the initialization declares, and every name it mentions;
  the initialization's mentions and names; and the constants of the
  initialization the document reads as values anywhere, which decide the
  signatures the initialization offers its closures. A unit of proposal is a strongly connected component of the
  graph of these mentions, the initialization one of its nodes
  (`pipeline/unit-slices.mts`); units are proposed after the units they
  read.
- *Slices.* A unit's slice is the document with the unit's members whole,
  each function its members (and the initialization, where the slice holds
  it) mention with its body left out, the initialization where a member
  mentions a name it declares, and every other function and top-level
  statement left out. The positions after each interval left out move back
  by its length, an interval holding kept code is kept, a name the parser
  makes at a position (`%…@N`) names the moved position, and the document's
  own declarations are named by module `local`, their name and their index
  among the declarations of that name. Another module's definition and
  an imported value's type hold that module's spans and spans of the
  document's reads of its members alike; a slice holds them with every
  span zero, each declaration's identity kept, a reference's type
  arguments at their mapped spans, and no written application, which the
  check alone reads. An edit of a function's body that keeps the
  functions and initialization names it mentions leaves unchanged the
  slice of every unit that neither holds it whole nor holds the
  initialization: a changed mention changes the units and the slices that
  hold the function by its signature, and an edit of the initialization, or
  of what it mentions, changes the slice of every unit that holds it.
- *Reads.* A unit's reads document holds its members, whether the
  initialization is one, the footprint and on-throw flag each function the
  slice holds by its signature settled on in its own unit's proposal
  (`producer --unit` prints them); where the slice holds the
  initialization, the constants read as values; and the qualified reads of
  the imports its code names. The producer solves footprints and on-throw
  flags for the unit's members alone, its neighbours fixed at those values.
- *Slice claims.* `producer --unit` also writes the slice's claims: its
  members' claims, and each function the slice holds by its signature
  proposed at the footprint and on-throw flag its reads document gives.
- *Assembly.* `producer --assemble` reads the units' proposals, maps each
  position, binding name and refusal span of a slice back to the document,
  and writes the document's claims as one proposal of the whole document
  would. A unit the producer refuses refuses the document's proposal, the
  initialization's refusal first, then in source order.

- *Search.* Each unit of the checked file is searched over its slice
  (`verifier --produce-unit`) at the slice's claims and the qualified reads
  of its code the importer's plan admits, its evidence written over the
  slice's store, with that store's heads and the unit's anchors beside it:
  each member's request with its labels marked, its search hints and its
  obligations' sequents (`FilePlans.anchors`). Its spans and its unit's
  name are mapped back to the document's positions outside every key.
- *Check.* One check (`verifier --check-units`) builds the document's front
  and writes each line's evidence over the document's store
  (`Translate.translate`, untrusted): the unit's requests in the slice and
  in the document are extracted from the same code, so each label of the
  slice's anchors is paired with the label at the same place of the
  document's, each pair of heads pairs their templates' labels, and a
  union pairs its members, a member whose image is known with that image
  and the others by their shape at the heads' signature classes. Every label
  of the evidence is renamed by that correspondence, and a union written in
  the slice's canonical order is written in the document's. Each unit is
  checked at the evidence so written (`lineVerdict`), as
  `checkUnitJson_safe` states. The check reads the whole document and
  executes after every edit of it.
- *One store per equation.* The pairing renames heads, one document head
  for each slice head: the document's store holds one head for equal
  templates where the slice's does, and orders them alike, so a union and
  the cases of evidence over it come in one order in both. The primitive
  kinds' heads are made first, after the primitive values'; compaction
  places the literal, scheme and primitive heads by their class of
  unfolding (`unfoldingClasses`), which no numbering enters. Every producer row has its head before
  the lowering's heads are hash-consed, and the hash-consing compares
  templates with their unions normalized after renaming (`hashCons`,
  `lean/Verification/Source/Equations/Finishing.lean`), so a row equal to a
  declaration's literal is one head whether or not a unit's extraction
  names it first.

The slices, the reads documents, the slice claims and the assembly's inputs
are stage inputs, keyed by their content; `pipeline/unit-slices.mts`, which
computes them, is outside every key.

## Observed stages

The parse and TypeScript's diagnostics read the file
system through the compiler and through Node, so their inputs are known only
after they run. Each is keyed in two steps. Its *pre-key* binds what is known
before it runs: its stage, its input files and paths, its implementation and
runtime, the active family descriptions and the compiler's identity. Its
*observations* are every answer the file system gave it, each a triple of an
operation, an absolute path and the answer:

| Operation | Answer |
| --- | --- |
| `read` | the SHA-256 of the bytes read, `directory`, or absent |
| `kind` | `file` or `directory` after following links, or absent |
| `real` | the real path, or absent |
| `dirents` | the digest of the directory's entries in name order with their own kinds (link, file, directory, other), including the digest of an empty list, or absent |
| `entries` | the digest of the directory's files and directories in name order, links followed and others dropped, or absent |

A failed lookup is an observation with the answer absent; configuration
discovery and module resolution are the queries they make. The stage's key is
the digest of its pre-key's manifest with its observations. An entry is
published under that key, then referenced from an index under its pre-key; a
reference is only a candidate: a later run with the same pre-key replays a
referenced entry that is valid, whose manifest is exactly its own pre-key
manifest with observations, and each of whose observations gives the same
answer when made again now. An entry is published only when its
observations are complete, as follows; otherwise the stage executes without
replay, its ineligibility recorded.

*Every read is an observation.* The front end reads the file system only
through [`tools/files.mts`](../tools/files.mts), which records each answer:
its own reads, the answers it gives the compiler, and the reads of Node's
resolver and loader where family activation uses them. A fast check
requires every module of the stages' code closure other than `files.mts`
and the module hooks it runs Node's resolver and loader through
(`tools/module-hooks.mts`) to import no file system, module or process API.

- *The compiler.* The compiler API delegates five queries to the client
  (`readFile`, `fileExists`, `directoryExists`, `getAccessibleEntries`,
  `realpath`), each falling back to the compiler's own file system when the
  client declines; its other operations (`Stat`, `WalkDir`, case-sensitivity
  detection, library location) use the compiler's file system directly. The
  front end answers all five, from its in-memory texts or from an
  observation of exactly the answer given; it declines only a path inside
  the compiler's own executable package (its library files), which the
  pre-key identifies. A failure of a query is the request's failure, as
  the front end's own read failure. On macOS the compiler runs under
  `sandbox-exec` with a profile that kills it on any read or existence test
  of a path outside the system volume (`/System` but its data volume,
  `/usr/lib`, `/dev`, the root directory and its links `/var`, `/tmp`,
  `/etc` themselves), its own executable package, its launcher and an empty
  working directory of the process's own, each allowed as named and as
  named through those links; three probes of the system's libraries
  (`~/.CFUserTextEncoding`, `/AppleInternal`, `/Library/Preferences/Logging`)
  are denied without the kill, answering absent every time. On Linux it runs
  under bubblewrap, in new namespaces whose file system holds only its
  executable package and the empty working directory, both read-only, and
  minimal `/dev` and `/proc`: any other path names nothing to it. Its
  environment is empty and it inherits no file but its standard streams. The
  allowed paths are fixed by the pre-key: the system's identity (macOS's
  build, Linux's kernel release), the installation's digest, the sandbox's
  configuration (the profile's text; bubblewrap's arguments and its
  executable's digest) and the case sensitivity of the executable's file
  system (the compiler's own probe). A compiler run that finishes therefore
  reached the user's files only through the five queries; on macOS a direct
  read, of an existing file or of a missing one, ends the run as an
  operational failure, and on Linux it finds no file
  (`tests/observed-stages.mts` makes both). Elsewhere the observations are
  incomplete.
- *Node's resolver.* A resolution of a specifier from module `m` observes the
  reads of [Node's resolution algorithm](REFERENCES.md#nodejs-modules). Each
  resolution first reads `m`'s package scope (`kind a/package.json` for each
  ancestor `a` of `m` from the nearest, stopping before a `node_modules`
  directory or at the first that is a file, its `read`, and the scope's
  directory `real`). A package import (`#…`) and a self-reference (the scope
  names the package and states non-null `exports`) resolve through it;
  another bare specifier of package
  `p` through the `node_modules` lookup
  (`kind a/node_modules/p` for each ancestor from the nearest, up to the
  first that is a directory, its `real` and the `read` of its
  `package.json`). The resolved file's `kind` and `real` follow. A relative,
  absolute or `file:` specifier observes its target's `kind` and `real`; a
  built-in, nothing. A package with absent or null `exports`, and a specifier
  a scope or a package found does not resolve, leave the observations
  incomplete.
  A package whose `exports` or `imports` resolve the specifier (the package
  found, or the scope of a self-reference or a package import) observes the
  `dirents` of every directory of its own tree, nested `node_modules` left
  out (a target naming `node_modules` is invalid); a symbolic link there
  leaves the observations incomplete, since the path a target names before
  Node resolves its links is not observed. A package import is accounted for
  only when every string target in its scope's `imports` map, through
  condition objects and arrays, starts with `./`. Any other string leaves
  the observations incomplete: another package lookup can traverse an
  unobserved link even when its resolved file lies inside the scope.
  Node reads these files itself: they are observed before and after the
  resolution, and the two must agree.
- *Node's loader.* Loading a module of a family's installation observes the
  bytes of each module the load reads (the source a load hook sees) and its
  package scope; a module read outside the installation leaves the
  observations incomplete.
- *The implementation.* Every module of the stage's code closure, the
  compiler package's and its executable package's files (its JavaScript
  client, its executable and its library files) are digested when the
  process loads them and are in the pre-key; a difference from disk at the
  stage entry or after execution before publication makes it ineligible,
  with the reason recorded and no entry published. The modules the
  front end loads at start-up are these.

*State follows the observations.* Each parse and each module lowering opens its parser fresh and
releases it at its end. A declaration compiler is opened for its collection
and released after it, or is a worker's
[retained declaration session](#retained-declaration-sessions). Every
compiler's ledger of every answer it was given is part of the observations
of each stage that uses it ([shared work](#shared-work)). The compilers' state is a function of the requests the
front end makes, which its code and inputs determine, and of answers the
stage's observations include. The process's own caches of file-system-derived values (installation roots and
inventories, activated guard tables, declaration origins) keep the
observations a value was computed from, and whether they were complete;
its first use in a stage makes them again, computing the value again where
one answers otherwise, and every use records them for the stage. Node's
resolution and module caches cannot be computed again: the
process keeps the first answer of every observation of its resolver and
loader, and an observed stage during which one answers otherwise fails as an
operational failure; the pipeline's worker process then exits, and a fresh
one takes its next check. A resolver or loader read the record cannot account
for marks the process for retirement and the current stage incomplete; that
stage keeps its result without publication. Further observed-stage execution
in the process is refused. Validated replays remain available because they
do not use Node's caches. The worker answers its current check and exits
when marked for retirement, so its next check has fresh caches.

*Validation.* An observation is made again by its operation, reading the
file system afresh. The answers a stage used are the ones it recorded: the
compiler's and the front end's reads by construction, Node's by agreement
before and after its read. A replayed entry is the stage's result for the
file system its observations describe, which agrees with the present one on
everything the stage reads.

Each imported module is proposed by the same units, slices and stages. Each
withdrawal recomputes the eligible reads and transitive claims assembly.
The plan of a document with qualified reads (`--module-runs`) prints each
module run: an imported module's document restricted to the read closure
of the functions the importer reads qualified of it, its initialization
kept. Each run is searched and checked in stages of its own, keyed on that
restricted document, so an edit of the importer that keeps the closure and
the module's lowered document replays them, and importers asking for the
same closure share their entries. The file's search and check cover its own
units only.
A replayed plan or search refusal drives the same withdrawal decision as a fresh
refusal. The orchestration and diagnostic presentation run under their
current implementation; a stored raw refusal is not a stored final Outcome.

## Retained declaration sessions

A worker of the pipeline's pool (`verify-source.mts --serve`, which the
census and the cases use) and the command line's one check retain one
*declaration session*: the compiler of a named project, kept between
collections of declarations
([`tools/declaration-session.mts`](../tools/declaration-session.mts)). The
parser is no session: each parse opens its own. A collection of an
automatically selected project opens a compiler of its own, releases it
after the collection, and releases the retained session.

*Compatibility.* A collection naming the project `p` with the resolution
file `f` uses the retained session when all of these hold:

1. the session's project is `p`, as a normalized absolute path, and its
   compiler's working directory is `dirname(f)`;
2. the session's compiler installation (`compilerChoice`) and the serialized
   active family descriptions are the collection's; the node-side code and
   the runtime are the process's, whose lifetime bounds the session's;
3. its ledger holds (below), the process's Node caches are consistent and
   not marked for retirement, and its base state is clean.

Otherwise the retained session is released, and a new one opened at
`dirname(f)`, with `p` opened by its first snapshot. Parses whose snapshot
directories differ share a session where their resolution files lie in one
directory; a collection of an import in another directory replaces it.
Releasing the worker, retiring it, ending the command or turning retention
off releases the session. A worker killed at its check's limit takes its
compilers with it: a compiler process ends when its channel to the worker
closes.

*Base state and restoration.* Between collections a session holds exactly
the project `p` open, no document open and an empty overlay. A collection
reacquires `p` in a snapshot of its own and checks what a fresh compiler's
collection checks: a strict configured project holding `f`, whose own
program reports no error. Its probes replace project files through the
overlay. After its result or its refusal, the collection restores the base
state: the overlay cleared, the compiler notified of every path a probe
replaced, the collection's snapshots released, and the new snapshot checked
to hold only `p`, with no overlay entry and no open document. The front end
counts a compiler's open documents at its snapshot requests, the only
requests that open or close one (`openDocuments`,
`tools/compiler-channel.mts`); a session's own requests name no file to
open, which its request function refuses. A tool failure releases the
session. A restoration that fails, or a state other than the
base one, releases it and makes every record being made incomplete, so the
attempt that used it publishes nothing.

*The ledger.* A session's ledger is a record kept over the session's
lifetime (`withLedger`, `tools/files.mts`): every answer its compiler and its
collections were given, a later query's, a diagnostics list's, a probe's and
a restoration's included, each with its Node-origin bit, and why it is
incomplete or inconsistent, if it is. Before a retained session serves a
collection, every answer is made again outside the records being made
(`validateLedger`): an answer that differs releases the session. Every Node
answer is made again, after one differs as well, against the process's first
answers; one that differs makes the process inconsistent, and the worker
retires. An incomplete or inconsistent ledger is never retained. The
validated ledger, its metadata included, is noted in every record being made
(`importLedger`), and every record begun while the ledger is kept, a nested
stage's or a process cache's computation, holds it from its start; so an
attempt's observations, and a cached value's, hold every answer the
compiler's state was computed from. The collection's new answers accumulate
in the ledger and in those records. At the end of each parse and diagnostics
stage, before publication, the ledger of every session the stage's
collections used is made again (`inDeclarationAttempt`), a session released
during the stage and a nested stage's included: one that does not hold makes
the attempt publish nothing, and releases its session if it is retained. These
checks keep the store's assumption that the file system is stable while a
stage reads it; they take no atomic snapshot of it.

*Keys.* The parse's pre-key binds the source's bytes, the snapshot path,
whose directory is the parser's working directory, the resolution file,
whose directory is the declaration compiler's, the named project or none,
and the active families; the diagnostics' pre-key binds the file, the
project and the families. A probe's overlay derives from these inputs and
the declarations read. The session's generation and the order of requests
are no inputs. An entry's key binds the ledger's answers with the stage's
own, so a session that read more gives an entry more observations: an
invalidation that may be wider than a fresh compiler's.

*Fidelity.* Conjectured: for fixed inputs and unchanged answers, a parse in
a reused session, its work shared ([shared work](#shared-work)), is the parse
in fresh compilers with no work shared, its Fragment or refusal and its
ordered diagnostics byte for byte. It rests on the compiler's caches being
correct across snapshots whose answers hold, on query omission and on the
exact restoration of the base state, a trusted obligation of the front end
([trust surface](DESIGN.md#trust-surface)) and no Lean result. The controls
of `tests/session-reuse.mts`, run by `make test-checks` through the production
adapters with replay disabled, compare each reused parse with the fresh one
at the same paths:

- forward, reverse and A–B–A orders, successes and refusals, distinct
  snapshot directories sharing one resolution project, one compiler opened
  and the parser opened by every parse; TypeScript's diagnostics between
  parses reuse the session and leave its base state, two ordered errors of
  a module among them;
- another project, resolution directory, family configuration, or an
  automatically selected project replaces the session; a snapshot path
  given other bytes, and project selection, are other inputs;
- a dependency first read by a later collection's query (a declaration
  file's real path, which the Fragment names) and one a later compiler
  request reads first (a configuration it parses) each enter the ledger and
  the stored entry; changing either replaces the session, the replacement's
  parse is the fresh one, and the entry no longer replays, while an
  unchanged entry replays opening no compiler; a probe's collection makes
  observations the session had not, each in its entry;
- any other changed answer of the ledger replaces the session and refuses
  the stored entry: a declaration, the configuration, an absent target
  created, a directory's entries, a link, a removed file;
- a probe-heavy collection (computed forms evaluated at applications) and
  shadowing locals among the compared parses;
- a record begun during a reused collection holds the ledger; a change, at
  an attempt's end, to what only a session the attempt used and released
  read, by itself or in a nested stage that ended before, publishes nothing;
- an incomplete read, a failed restoration, an overlay, a second project, a
  document of the project or outside it left open, and a request to open a
  document, publish nothing and release the session; an incomplete
  Node read also marks the process for retirement and refuses its further
  observed execution; a changed Node answer of the ledger makes the process
  inconsistent; a worker killed while it holds a session takes its
  compilers with it;
- the attempts' readings of each compiler that ended sum to its lifetime's
  time within its idle time (at most 20 ms or a tenth); an observed attempt
  around a parse and a non-observed attempt using a session counts, with
  them, what the process and the compilers used (within 30 ms or a tenth),
  and the non-observed attempt's record what was read around it (within
  15 ms or a tenth); a reading not taken makes the attempt's CPU time
  unavailable.

*Measured.* Two cold censuses of `tools/` on one machine (2026-10-23, each
in a fresh store, 300 s step limit, 12 workers), of 49ff119 with a
compiler per collection and of 5ce25e3 with retained sessions: over the 404
slices whose source both share, parse CPU 1,385 s and 857 s, the CPU of all
executed stages 3,321 s and 2,862 s; the 404 outcomes equal, and of their
parses 329 byte-identical and 75 differing only in the source offsets of
declarations in front-end files whose text the two commits differ in.

## Shared work

Work whose result depends only on its inputs is kept and served again,
each kind at the lifetime its inputs fix, its read set the observations it
was computed from, as a computation's dependencies are what it read in
[SKStore](REFERENCES.md#skstore). Store
entries and process caches are described above; within a process three
further kinds of work are kept.

*Attempt answers.* Within an attempt (the outermost observed stage's record
being made), the front end's own `kind`, `real`, `dirents` and `entries`
operations at a path answer what they answered first in the attempt, and
the answer is noted again in every record being made (`attemptAnswer`,
`tools/files.mts`). Three kinds of read stay fresh: a read outside every
record (a ledger's validation suspends them); a read standing for Node's
(a Node-origin observation, and every read of the probes before and after
Node's resolution, `fresh`), so that their agreement and the process's
first answers compare the file system's answers; and `read`, whose bytes
the caller uses.
The store's assumption that the file system is stable while a stage reads
it is thereby made operative for the front end's own reads: the attempt's
computation is a function of the answers its record holds. A path whose
answer changes between two of the front end's reads in one attempt is not
seen within it; the end-of-stage ledger validation and the replay's
validation remain the checks of stability.

*Resolutions.* Node's resolution of a specifier from a module
(`nodeResolve`) is a process cache: resolved once, its observations made
again at its first use in each attempt (`remembered`).

*Compiler ledgers and query answers.* Every front-end compiler has one
ledger, every answer the file system gave it over its lifetime, kept by
its channel (`compilerLedger`, `tools/compiler-channel.mts`): a retained
declaration session's is the session's ledger, and a compiler opened for
one parse or one collection has its own. Before every request the channel
notes the compiler's ledger in each record being made that does not hold it
yet (`importLedger`), and the request runs with the ledger kept, so its
answers reach the ledger and every record being made. Records are made in
a stack and a ledger grows only while it is kept: every record holding a
ledger that is still being made sees every later answer, incompleteness and
inconsistency of it, so a record is noted a ledger once. A query of a
snapshot, a request of the channel's audited list (`snapshotQueries`) whose
parameters name an unreleased snapshot, is served the text the snapshot
first answered to the same method and parameters; a snapshot's answers go
with its release. It rests on a conjecture, *query omission*: asking such a
query again answers the text it first answered, and omitting the repeated
request changes no answer the compiler gives afterwards to any request, of
that snapshot or another, over its lifetime.

*Imported modules.* Each program module a parse reaches is lowered by a
stage of its own, `module`, nested in the parse (`moduleCall`,
`pipeline/parse-stage.mts`): the module's lowering as a run of that module
alone lowers it, in a parser compiler of its own at the module's directory
(`lowerModule`, `tools/fragment-parse.mts`), its value the module's entry
as text, its imports, or the gate's refusal. Both its compilers, the
parser's and a declaration session of its own released after it, read the
named project rooted at the module (`moduleProject`,
`tools/declaration-session.mts`): the project's options, its root files the
module and the declaration files among the project's roots, which state
what every file of it sees, held as a configuration of its own beside the
project's that no probe replaces. A collection that names no project reads
the project its file belongs to, every file of it. The parse releases its own
parser compiler before it lowers a module, and splices each module's text
into its Fragment in the order it reaches the modules, the bytes
`JSON.stringify` writes of the same value. A nested invocation is forced and
recorded as its enclosing one is (`invokeNested`). Executed, the module's
answers are noted in the parse's record as they are made; replayed, its
file-system observations are made again while the parse's record is made:
either way the parse's observations hold them. A module's read set holds
what its compilers read: the module, the modules it imports, the project's
configuration and declaration files, and the host libraries it reaches. An
edit of an importer, or of another module, changes none of it, and the
module's entry replays. A process cache's value computed while a compiler's
ledger was kept is used again only while that ledger is kept, and computed
again elsewhere (`remembered`, `tools/files.mts`), so a module's record holds
no answer of the importer's compilers.

*Named inputs read.* The run's tag selection of each host family
(HOST-FAMILIES.md, residuals) is computed by the checked file's parse and
given to every module it lowers. A module's lowering reads it by family, at
one site (`familySelection`, `tools/declaration-graph.mts`), and each read is
an observation `["input", "selection/<marker>", <the tags as JSON, or null>]`
of the module stage's record alone (`noteInput`, `tools/files.mts`). A
candidate entry replays when each input observation answers the same for
the invocation's own selection (`observed.inputs` of its call) and each
file-system observation holds; input observations are never noted in the
enclosing parse's record, which computed the selection from its own reads.
An execution publishes only where its invocation answers each input read as
recorded. Every process cache's computation being made when a named input
is read, within the stage or around it, is incomplete, and its value is kept
for none. A module consulting no family, or the same families at the same tags,
shares one entry across runs whose selections differ elsewhere.

*Tests.* `tests/shared-work.mts` shows, without a stage: a later read of an
attempt answering its first answer and noting it in a record begun after
it; the next attempt, a ledger's validation and a Node-origin read reading
afresh; a change within an attempt seen with sharing off; a repeated query
of a snapshot served, another snapshot's asked and a released snapshot's
answers gone; and a compiler's ledger held by every record that uses the
compiler, a record holding it seeing its later growth and incompleteness. The
fidelity controls of `tests/session-reuse.mts` compare each parse, its work
shared in a reused session, with the parse in fresh compilers with no work
shared (`sharingForTests`), byte for byte. `tests/observed-stages.mts` shows a
parse executing again replay its modules' entries, a module's change miss
its own entry alone, and an importer's edit replay every module's; and, in a process of its own (`--selection`), a module's entry
replay where an unconsulted family changes and miss where a consulted
family's tags change or it is absent, a module consulting no family replay
across selections, no input observation reach the enclosing record, and a
process cache reading an input, or around a stage reading one, be kept for
none, and a stage whose call does not answer its input publish nothing. The
Fragments of every pipeline case, parsed with the importer's parser compiler
and with module stages executed and replayed, are equal (measured
2026-10-24, all 2,081).

## Locations

Stages use stable file identities and execution locations
independent of an invocation's temporary artifact directory. The parser
retains the original source's project and import-resolution context.
Any path affecting resolution, document identity or output remains an
input unless an explicit stage adapter establishes a stable equivalent.

The source snapshot lives at a store location named by its bytes and its
configuration's; its path is the Fragment's file identity, which every
later document embeds. A process stage runs in a fresh directory holding
its input files under fixed role names, with relative arguments and an
explicit environment. The audited programs, the repository's builds of the
verifier and the producer and the controls' mutation verifier, read only the
files their arguments name and do not observe that directory's path, which
is excluded from the key. Any other program executes without replay.

Logs belong to the stage invocation whose paths they describe. Each
caller receives fresh writable copies of the artifacts under its own run
root, and its Outcome names that directory. Shared entries are immutable.
Programmatic checks remove their directories
once their result is assembled. A consumer that reads artifact files requests
`retainArtifacts` and binds the result with `using`; leaving that scope removes
the directory, including when the consumer throws. The census reads its logs
within that scope. Command-line inspection explicitly keeps its run root.
New runs stop the driver with a resource error when the artifact volume has
less than 10 GiB available. The run root is excluded from semantic keys only
where stage execution is independent of it. Store data outlives run directory
cleanup.

## Entries and timeouts

A finished entry contains the complete input
manifest, exit status, stdout, stderr and a manifest of output files with
their digests. This includes parser diagnostics and auxiliary stage outputs.
Only a complete success or recognized refusal is a finished result.
Operational failures are not reusable results. A stage stopped at its memory limit is
an operational failure: it is reported as a tool failure naming the memory
read and the limit, and nothing is published.

A timeout is a separate immutable observation recording its stage key,
attempt identity, elapsed execution time, CPU time up to the kill, enforced
limit and resource policy. Limits and measurement metadata are outside the stage key. Under the
same resource policy, a request may reuse an observation whose enforced
limit is at least the requested limit. A larger requested limit executes the
stage. If no finished entry is available, retrying timeouts
(`TSCERT_RETRY_TIMEOUTS=1`) bypasses timeout reuse and executes at the
requested limit. The retry flag is outside the key; normal timeout
publication and resource-policy checks apply. Force execution bypasses both
finished results and timeout observations. Reuse reports an earlier timeout, not proof that execution
would time out again.

An aggregate worker deadline records interruption of the run. A stage
timeout requires identification of the attempt and evidence that its own
enforced limit expired; identifying the active stage alone is insufficient.
Completed entries remain reusable. Readers check for a finished entry before
returning a timeout observation; a finished entry visible at that check
takes precedence.

## Publication

Writers build complete entries in unique temporary
directories on the store's filesystem, close their files and publish by
atomic rename to the stage-key destination. Published entry directories are
nonempty and immutable. A destination-exists failure requires validation of
the existing entry. Finished results are compared by input manifest, exit
status, stdout, stderr and output-file names and digests; attempt
identities, timings and load measurements are excluded. Different result
payloads for one key are a store error. If the existing entry is invalid,
the caller may use its freshly computed result without publishing it;
replacement requires coordinated removal of the invalid entry.

One process executes a replay-eligible key at a time. Before executing, it
claims the key: the lock `running/<stage>/<key>`, acquired as the eviction
lock is ([the lock](#location-and-size)), so a claim present names its
owner, a claim of a stopped owner or without an owner file is taken over,
of two processes taking one over the one whose claim is in place keeps it,
and a release removes only its own claim (`Store.claim`). A process finding
a key claimed by another running process waits, looking every 50 ms for a
finished entry or a timeout observation at the key, which it replays, or
for the claim's removal, after which it claims the key itself; after twice
the stage's limit (`claimWaitMs`), past which the holder's execution has
been killed, it executes the key itself. So within a run, and across the
runs sharing a store, each key executes once while its result is
published.

Finished entries and timeout observations have separate destinations.
Publication never deletes a timeout entry to replace it with a finished
result, so a late timeout cannot overwrite success. Duplicate computation
is permitted.

Timeout observations use unique attempt destinations and the same
complete-directory publication protocol. Concurrent observations coexist.

Atomic publication provides visibility across process interruption.
Power-loss durability requires a separately specified and validated
filesystem flush protocol. Readers validate complete manifests, an integrity
digest covering every manifest payload field (including exit status and
measurement metadata), and file digests; missing, incomplete or corrupt
entries cause recomputation.
Cleanup removes temporary directories only when their writers are known
to have stopped. A reader reads a whole entry into its memory and validates
that copy before use; concurrent eviction causes a retry or miss.

## Replay and trust

The parser is part of the trusted source boundary.
Replaying its output and replaying a successful check additionally trust
the store implementation, its binding of results to exact inputs and the
integrity of its stored results. A replayed parse further trusts that its
observations are complete: the compiler's sandbox and the compiler API's five
queries for the compiler, the resolution algorithm's reads for Node's
resolver, and the process's first-answer consistency for its caches
([observed stages](#observed-stages)); a parse executed in a retained
session further trusts the session's obligations
([retained declaration sessions](#retained-declaration-sessions)). The store
is private to the user and
shared among that user's cooperating processes. Digests detect accidental
corruption; they do not authenticate results supplied by an untrusted
writer.

`SourceClaimJson.checkUnitJson_safe` establishes safety from the corresponding
accepted `unitVerdict` evaluation. The memoizer must preserve that premise
when replaying a check. This is an additional implementation obligation,
outside that theorem.

The production check's pure computation supports a deterministic judgment
for fixed inputs. Replay eligibility requires an audit of the executable's
I/O and runtime dependencies. Cold and replayed runs are compared across
different run roots and worker histories, including their judgments,
documents and diagnostics. These checks support the implementation audit;
they are not a proof of executable determinism. Resource timeouts are
observations rather than deterministic judgments.

## Controls

A control tests the verifier, the producer or the pipeline on
an input no case makes: a forged or tampered document, a mutation of the
verifier, an injected tool failure, a host-family override. The controls of
`pipeline/test.mts` run in `make test-checks`, in a pool of processes. Every
operation a control runs is a stage invocation of the common mechanism and
replays from the store like any other: its key binds the executable by
content, its argument vector, its environment and the bytes of every input
file, so the operation executes again exactly when one of these changes. A
control's own code (its forgery and its assertions) runs every time, over
the operation's result, executed or replayed.

- *Executables.* The repository's verifier and producer builds, and the
  mutation verifier. The mutation verifier is built at each run of the
  controls from the current build's generated C and Lake's link response,
  and is audited as the verifier is: its identity is its executable's digest
  and linked libraries, and it reads, beyond the verifier's I/O, only the
  variable `TSCERT_TEST_MUTATIONS`, which its invocation's environment
  fixes. A mutation selection is therefore part of the key, and a rebuild
  giving the same bytes replays its entries.
- *Protocol.* The exit protocol that decides whether an exit is a finished
  result (the refusal's status and prefix) is part of the key.
- *Settings.* A host-family override is an input of the parse (the active
  family descriptions). An injected tool failure is written into a stand-in
  program, which no audit identifies: its invocations execute every time,
  and the stages it does not replace replay.
- *Baselines.* A control deriving its input from a case's honest documents
  obtains them through the pipeline: the case is checked (its stages
  replayed when warm) and its outcome required to be the case's expected
  one.
- *Ran.* Each operation's attempt must have executed, or replayed a finished
  result the store holds for its key; a replayed timeout fails the control.
  `TSCERT_STAGE_STORE=off` executes every operation of every control.
- *Limit.* A control's operation is killed after 30 s unless the control
  states another limit (`tested`, `pipeline/stages.mts`).

The controls of the store itself (`tests/stage-store.mts`, the observed
stages' replay controls, the cold and warm comparison of `pipeline/test.mts`)
name fresh stores of their own and execute every time: their subject is the
replay mechanism. Store tests cover dependency invalidation, concurrent
publication, interrupted writers, timeout/success races, writable
artifact isolation and eviction: least recent use within the budget, items
no use line names measured, references going with their entry, a held
snapshot kept, a snapshot's use during a removal doing without the store's
snapshot, markers per process, a use before a removal's second read of the
use logs keeping its snapshot and one after it doing without, the lock
taken over from a stopped or missing owner and never from a running one
(also when another process takes it over first, or acquires it while it
is being put back), a release removing only its own lock, another host's
owners running until a clean forgets the host, each timeout observation an
item, a replay racing
passes a miss or the entry's own result, and a pass an orchestrator starts
leaving the store within its budget. The replay control evicts its store
whole and runs again: every stage executes, to the same outcome, documents
and logs. The edit replay control of `pipeline/test.mts` edits an importer
of a certified module in its own code: the module run's search and check
replay, the importer's search executes, and the edited run's outcome is a
cold run's in a fresh store.

## Timing

Every invocation records monotonic elapsed wall time, its
configured limit and whether it executed, replayed, timed out, failed
operationally or was interrupted. Replay records lookup, validation and
materialization time separately from the stored execution measurements. An
execution, a timeout included, also records its CPU time (user and system),
the processes it covers and the largest peak memory among the stage's
processes; a replay records the stored execution's, a finished entry's or a
timeout observation's. A measurement that is not taken is recorded as
unavailable, with its reason.

- A process stage's program runs under the stage runner
  ([`pipeline/runner/stage-runner.c`](../pipeline/runner/stage-runner.c),
  built by `make build-runner`), which starts it with the invocation's
  arguments, environment, working directory and standard streams in a
  process group led by a watchdog. The runner enforces two limits: the
  time limit, and a memory limit on the program's current physical
  footprint, read every 200 ms (on macOS compressed and swapped pages
  included, on Linux the resident set and swap; `TSCERT_STAGE_MEMORY`
  gibibytes, 8 by default). At either limit, or on SIGTERM, SIGINT, SIGHUP
  or SIGQUIT, it continues and signals the program, by its process id, and
  the group (SIGTERM at a limit), and
  250 ms later kills them, so a program ignoring SIGTERM, stopped, or out of
  the group ends too. Its standard output and standard error are files the
  adapter opens and unlinks before the runner starts and reads whole when
  the runner ends, so an output's size is bounded by the file system alone.
  When the program ends, the runner kills what remains of its group and
  ends with the program's exit status or signal. The watchdog holds a pipe only the
  runner writes to; when the runner ends in any way, the watchdog kills the
  group. Node kills the runner 2 s past the grace period, a backstop for a
  runner that does not end. A failed system call of the runner's kills the
  program and the group and fails the run.
- Containment is limited to the program and its group: a descendant that
  left the group (`setsid`, `setpgid`) is not killed, and neither is a
  program that left the group when the runner itself dies. Such a
  descendant may still write to the output files after the adapter reads
  them; what it writes then is not part of the result. TScert's process stages, the Lean verifier and the
  OCaml producer, start no process.
- The runner's report, the `RUSAGE_CHILDREN` CPU time and peak resident set
  (`ru_maxrss`) of the program and the descendants it waited for, whether
  the limit expired, and any failure of its own system calls, goes to its
  descriptor 3, a file the program does not inherit; it covers the CPU time
  used up to a timeout's kill. Descendants the program did not wait for are
  not counted. The runner relays the exit status a result is classified by
  and decides timeouts, so it is part of the execution adapter: a process
  stage's key covers its identity.
- An in-process stage records the pipeline process's own CPU time over the
  attempt (`process.cpuUsage`) and adds, for each compiler
  process running during it (`tools/compiler-processes.mts`, which names a
  process by a generation a reused process id does not repeat), the
  difference of two readings by `stage-runner --cpu <pid>`: at the start of
  each interval in which the attempt is the innermost one running, or zero
  for a process started during it, and at that interval's end, or just
  before the process's channel closes, after the requests releasing its
  snapshots. A retained compiler's time is therefore divided among the
  attempts that use it, its idle time counted by none, and its validation
  and restoration by the attempt they belong to. A nested attempt's time,
  the pipeline process's and the compilers', is its own and not its
  enclosing attempt's. The reading is
  `proc_pid_rusage` on macOS, to the microsecond, with the compiler's
  lifetime maximum physical footprint as its peak memory, and
  `/proc/<pid>/stat` and `VmHWM` on Linux, to the clock tick, over the
  compiler's process and its descendants, since its sandbox runs it as one
  (their peaks summed); an attempt with
  a reading not taken records its CPU time as unavailable. The pipeline
  process's own peak memory is not attributed to a stage.

Timing, CPU and memory are outside semantic keys and result equality.
Census records retain these measurements for each attempt, including module
stages and withdrawals, after entry eviction. They describe observed
execution cost. Elapsed time depends on the machine's load; CPU time does not
count waiting.

A census's stage-cost table sums the producing measurements its file
records reference, each stage result once, by its stage and key. A replay
refers to a historical producing execution, so those sums describe recorded
costs, rather than CPU consumed by the current census. Peak memory is a maximum, not a sum. The census record's
elapsed time measures that run's wall time, including replay and scheduling.

A fixed-input performance comparison states the source or request, claims,
mode and arguments it holds fixed, the executable for each run, and their
outcomes. A source change that passes an earlier refusal can expose more
proof work; aggregate census costs alone do not establish the cost of the
same proof obligation.

## Location and size

The store lives outside every checkout at
`$XDG_CACHE_HOME/tscert/stages`, defaulting to `~/.cache/tscert/stages`.
`TSCERT_STAGE_STORE` selects another directory; `off` forces execution.
The store keeps itself within a size budget, `TSCERT_STORE_BUDGET`: a
number of bytes with an optional `K`, `M`, `G` or `T` suffix (powers of
1024), 15 GiB by default. Eviction is approximate and affects reuse only;
readers treat concurrent removal as a miss.

*Items.* An eviction pass accounts four kinds of item: a finished entry, a
timeout observation, a source snapshot, and an observed stage's
reference, which belongs to the entry it names. An item's size is the bytes
its files take in whole 4 KiB blocks, the allocation unit of the volume:
most of the store's files are smaller than one block.

*The use log.* Every process using the store appends to a use log of its
own, `uses/<host>.<pid>.<id>`, one line `<ms> <bytes> <item>` for each
item it publishes and, at most once per ten minutes for each item, for each
item it reuses. A publication's line is written before its rename. The
use log gives each item's size and last use in one line read in sequence;
ordering items by modification time instead would read the status of every
file of the store, millions of them. Least recent use orders the
generations of entries that edits of keyed files produce: a generation no
checkout's code names any more stops being used and goes first, and an entry
every checkout reuses (a check whose verifier and inputs no edit changed)
stays whatever its age.

*Owners.* A lock, a marker and a use log name their owner: a host, a
process and a random id. An owner of this host runs while its process is
alive. This host cannot see another host's processes, so an owner of
another host counts as running until a clean names that host as forgotten
(`make clean-store FORGET_HOST=<host>`); until then its holds stay, its
marker keeps uses off the store's snapshots and its lock stops passes.

*The lock.* A pass holds the store's eviction lock, the directory
`eviction/` holding its owner's name. The directory is built whole in a
temporary directory and renamed into place, so a lock present names its
owner. A lock whose owner has stopped, or one without an owner, is taken
over: renamed into the taker's temporary directory and deleted there where
it still names the owner judged stopped (or still has none); otherwise it is
renamed back, and where another lock took its place meanwhile, it stays in
that temporary directory, which goes once the taker has stopped. The holder
releases its lock the same way, deleting it only where it names its own
id. The lock keeps passes from repeating each other's work; two passes at once remove
nothing a running process holds either, since each removal of snapshots has
a marker of its own and every other removal is a rename a reader sees
whole.

*A pass.* It reads the
pass summary (`uses/base`, one line per item, written by the previous
pass) and every process's use log, and lists the store's entry, timeout
and snapshot directories. An item listed that no line names is measured
from its files, its latest modification time standing for its last use; an
item named and not listed is dropped; a reference whose entry is not
listed is removed. A store without a summary also has its references listed.
Where the items take more than the budget, the pass removes the least
recently used ones until they take at most 80% of it, so that a pass that
removes is followed by passes that only read; an entry goes with its
references, and a pre-key directory left empty with them. An item is
removed by renaming its directory into the pass's temporary directory and
deleting it there: a reader sees it whole or absent, and a writer whose
destination's parent a pass removed creates the parent again. The pass then
writes the summary, folding in the use logs of the processes that have
stopped, and removes those files where their processes are still stopped.

*When a pass runs.* The orchestrators (the case runner, the census and the
controls) start a pass as they begin where one is due: none is running and
none finished in the last ten minutes. The pass runs in a detached process
of its own, `node pipeline/stages.mts evict`, which prints its summary when
run by hand; the orchestrator does not wait for it. Between two passes the
store exceeds its budget by at most what is published meanwhile. On a store
of 30,112 items taking 1.8 GB (the suite run from two checkouts), a pass
removing nothing took 0.3 to 0.5 s, one measuring every item 3.8 s, and one
removing 19,581 entries, 2,431 snapshots and 4,392 references down to
0.4 GB took 23 s, most of it the system deleting files; a warm `make test-cases`
took 18 s with the use logs and 18 to 20 s without them. On a copy of the
shared store (392,759 items, 14.9 GB: 241,707 snapshots, 151,052 entries
and timeout observations), the first pass, measuring every item, took 392 s; the
next one 3.5 s; and one removing 119,224 entries and 43,053 references
down to 3.4 GB 126 s (measured 2026-10-29).

*Snapshots in use.* A source snapshot's path is the Fragment's file
identity, and the parse reads the snapshot through the compiler. A process
writes a line for a snapshot in its use log before validating it, and no
pass removes a snapshot that a running process has named. Snapshots are
removed under a marker of the removing process,
`evicting/<host>.<pid>.<id>`: the process creates the marker, reads the
running processes' use logs again, moves out the snapshots none of them
holds, and deletes its marker. A use that finds a running process's marker,
after writing its line, parses its own snapshot in the run's directory
instead, at once. Either the use's line precedes that second read, and the
store's snapshot stays, or the marker precedes the use's check, and the use
does without it. An entry needs no hold: a reader copies it whole and
validates the copy, so an eviction during a replay is a miss.

*Cleaning.* `make clean-store` waits for a running pass, then removes every
finished entry, timeout observation and reference, every source snapshot
no running process holds (under a marker of its own), the abandoned
publication directories on this host, the pass summary, and the use
logs and markers of stopped processes. `FORGET_HOST=<host>` counts that
host's owners as stopped for the clean.

## Census records

Each census file has a persistent record of its source identity, its units'
results, its omissions, execution policy and ordered invocation references,
including module stages and withdrawal attempts. Each reference identifies
its attempt and, where available, its complete stage key. These records survive artifact
cleanup and store eviction. Processes may partition the files and share
stage entries. A later census runs the current orchestration and presentation, validating
dependencies through the common stage mechanism. Census records retain
historical outcomes and measurements; they do not independently authorize
replay of a final Outcome. Missing stage entries execute again.
