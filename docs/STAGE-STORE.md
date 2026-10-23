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
- `tools/unchecked.mts`, `tools/shadow-contracts.mts`: the `any` audit of the
  node side's sources, a suite;
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
identify and a process stage's inputs, never an observed stage's inputs.

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
cannot be identified executes without replay.

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
| parse | source bytes and logical identity; project and resolution context; active host-family descriptions; the complete filesystem observations of parsing, declaration collection and host activation |
| lower | the exact Fragment document |
| propose | the exact Fragment, flow and qualified-read documents, including whether the optional argument is present |
| assemble claims | the raw proposal and ordered transitive module-claim documents selected by the reads |
| search | the exact Fragment and assembled claims; explicit file identity; source snapshot binding; search depth and subtype rounds |
| check | the exact Fragment, assembled claims and evidence; explicit file identity; source snapshot binding; subtype rounds |
| explain | the Fragment and flow passed to the producer's `--explain` mode |
| TypeScript diagnostics | source identity, project context and the complete compiler dependency observations |

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
requires every module of the stages' code closure other than `files.mts` to
import no file system, module or process API.

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
  are denied without the kill, answering absent every time. Its environment
  is empty and it inherits no file but its standard streams. The allowed
  paths are fixed by the pre-key: the operating system's build, the
  installation's digest, the profile's text and the case sensitivity of the
  executable's file system (the compiler's own probe). A compiler run that
  finishes therefore reached the user's files only through the five
  queries; a direct read, of an existing file or of a missing one, ends the
  run as an operational failure (`tests/observed-stages.mts` makes both).
  Elsewhere the observations are incomplete.
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

*State follows the observations.* Each parse opens its parser fresh and
releases it at its end. A declaration compiler is opened for its collection
and released after it, or is a worker's
[retained declaration session](#retained-declaration-sessions), whose ledger
of every answer its compiler was given is part of the observations of each
stage that uses it. The compilers' state is a function of the requests the
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

Each imported module uses the same lower and propose stages. Each
withdrawal recomputes the eligible reads and transitive claims assembly.
A replayed search refusal drives the same withdrawal decision as a fresh
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
`dirname(f)`, with `p` opened by its first snapshot. Slices whose snapshot
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
to hold only `p`, with no overlay entry. No request of a session names a file
to open, which its one request function refuses, so it holds no open
document. A tool failure releases the session. A restoration that fails, or a state other than the
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
collections used is made again (`settleDeclarationSession`), a session
released during the stage included: one that does not hold makes the
attempt publish nothing, and releases its session if it is retained. These
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
a reused session is the parse in fresh compilers, its Fragment or refusal
and its ordered diagnostics byte for byte. It rests on the compiler's caches
being correct across snapshots whose answers hold and on the exact
restoration of the base state, a trusted obligation of the front end
([trust surface](DESIGN.md#trust-surface)) and no Lean result. The controls
of `tests/session-reuse.mts`, run by `make test` through the production
adapters with replay disabled, compare each reused parse with the fresh one
at the same paths:

- forward, reverse and A–B–A orders, successes and refusals, distinct
  snapshot directories sharing one resolution project, one compiler opened
  and the parser opened by every parse; TypeScript's diagnostics between
  parses reuse the session and leave its base state;
- another project, resolution directory, family configuration, or an
  automatically selected project replaces the session; a snapshot path
  given other bytes, and project selection, are other inputs;
- a dependency first read by a later collection (a declaration file's real
  path) enters the ledger and the stored entry; changing it replaces the
  session and the entry no longer replays, while an unchanged one replays
  opening no compiler; so does any changed answer of the ledger: a
  declaration, the configuration, an absent target created, a directory's
  entries, a link, a removed file;
- a probe-heavy collection (computed forms evaluated at applications) and
  shadowing locals among the compared parses;
- a record begun during a reused collection holds the ledger; a change, at
  an attempt's end, to what only a session the attempt used and released
  read publishes nothing;
- an incomplete read, a failed restoration, an overlay, a second project or
  a document left publish nothing and release the session; an incomplete
  Node read also marks the process for retirement and refuses its further
  observed execution; a changed Node answer of the ledger makes the process
  inconsistent; a worker killed while it holds a session takes its
  compilers with it;
- the attempts' readings of each compiler that ended sum to its lifetime's
  time within its idle time (at most 20 ms or a tenth).

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
The run root controls artifact lifetime; it is excluded from semantic keys
only where stage execution is independent of it. Store data outlives run
directory cleanup.

## Entries and timeouts

A finished entry contains the complete input
manifest, exit status, stdout, stderr and a manifest of output files with
their digests. This includes parser diagnostics and auxiliary stage outputs.
Only a complete success or recognized refusal is a finished result.
Operational failures are not reusable results.

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
observations are complete: the sandbox profile and the compiler API's five
queries for the compiler, the resolution algorithm's reads for Node's
resolver, and the process's first-answer consistency for its caches
([observed stages](#observed-stages)); a parse executed in a retained
session further trusts the session's obligations
([retained declaration sessions](#retained-declaration-sessions)). The store
is private to the user and
shared among that user's cooperating processes. Digests detect accidental
corruption; they do not authenticate results supplied by an untrusted
writer.

`SourceClaimJson.checkJson_safe` establishes safety from the corresponding
successful `checkJson` evaluation. The memoizer must preserve that premise
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
`pipeline/test.mts` run in `make test`, in a pool of processes. Every
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
publication, interrupted writers, timeout/success races and writable
artifact isolation.

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
  process group led by a watchdog. The runner enforces the limit: at the
  limit, or on SIGTERM, SIGINT, SIGHUP or SIGQUIT, it continues and signals
  the program, by its process id, and the group (SIGTERM at the limit), and
  250 ms later kills them, so a program ignoring SIGTERM, stopped, or out of
  the group ends too. When the program ends, the runner kills what remains
  of its group, so no descendant in it holds the output pipes, and ends with
  the program's exit status or signal. The watchdog holds a pipe only the
  runner writes to; when the runner ends in any way, the watchdog kills the
  group. Node kills the runner 2 s past the grace period, a backstop for a
  runner that does not end. A failed system call of the runner's kills the
  program and the group and fails the run.
- Containment is limited to the program and its group: a descendant that
  left the group (`setsid`, `setpgid`) is not killed, and neither is a
  program that left the group when the runner itself dies. Such a
  descendant may also hold the output pipes, keeping the invocation waiting
  until the backstop. TScert's process stages, the Lean verifier and the
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
  attempt (`process.cpuUsage`); an observed one adds, for each compiler
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
  `/proc/<pid>/stat` and `VmHWM` on Linux, to the clock tick; an attempt with
  a reading not taken records its CPU time as unavailable. The pipeline
  process's own peak memory is not attributed to a stage.

Timing, CPU and memory are outside semantic keys and result equality.
Census records retain these measurements for each attempt, including module
stages and withdrawals, after entry eviction. They describe observed
execution cost. Elapsed time depends on the machine's load; CPU time does not
count waiting.

## Location and size

The store lives outside every checkout at
`$XDG_CACHE_HOME/tscert/stages`, defaulting to `~/.cache/tscert/stages`.
`TSCERT_STAGE_STORE` selects another directory; `off` forces execution.
`make clean-store` removes finished entries, timeout observations and
abandoned publication directories on this host. It retains
immutable, content-addressed source locations, validated at each use, so
active parses keep their inputs.
Eviction is approximate and affects reuse only; readers treat concurrent
removal as a miss.

## Census records

Each slice has a persistent record of its source
identity, outcome, execution policy and ordered invocation references,
including module stages and withdrawal attempts. Each reference identifies
its attempt and, where available, its complete stage key. These records survive artifact
cleanup and store eviction. Processes may partition the slices and share
stage entries. A later census runs the current orchestration and presentation, validating
dependencies through the common stage mechanism. Census records retain
historical outcomes and measurements; they do not independently authorize
replay of a final Outcome. Missing stage entries execute again.
