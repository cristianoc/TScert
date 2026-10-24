# Draft: each piece of front-end work done once, keyed by its inputs

A design for the census's parse cost and the verifier's input preparation.
Its stages and their status are in [WORK](../../WORK.md#status). Base: TScert
main at 297120f.

**Evidence labels.** **Measured** names the run that produced a number.
**Cited** names inspected code. **Conjectured** marks a proposed design, an
estimate or a proof obligation.

## 1. Current state

**Measured — census of 6a3a864** (2026-10-24, cold store, 466 slices, 12
workers): about 1,520 s of executed stage CPU, 61% parse (932 s), 22% search,
8% propose, 4% explain, 3% check. Raw data in the 2026-10-24 measurement's
scratch directory, outside the repository.

**Measured — the parse's phases** (every census parse replayed at 6bbc6f1
in 6 processes):

| Phase | Share |
| --- | ---: |
| collecting the main slice's declarations | 48.5% |
| collecting imported modules' declarations | 22.9% |
| the parser's compiler building the project's program on opening an imported module | 11.2% |
| validating a session's ledger before reuse | 4.9% |
| opening the parser's compiler, once per parse | 4.8% |
| validating the ledgers again before publication | 3.1% |
| the rest | 4.6% |

**Measured — repetition inside one collection.** 6.6 M synchronous compiler
requests over the census (about 14 k per slice); 4.16 M `realPath` calls
taking 201 s, each a `realpathSync` and an observation, made per declaration
identity (`idOf`, `identityOf`, `libraryFile`, `familyOfFile`); 26.9 k
`nodeResolve` calls taking 78 s (from `importedExport` and
`activatedModules`), each observing its resolution twice and each
observation walking the `typescript` package's tree (`observePackageLinks`).

**Measured — repetition across slices.** Six imported modules are lowered
82 times (239 s against 10 s once each; `fragment-support.mts` 47 times).
The 466 slices have 434 distinct texts: a group of mutually recursive
functions gives each of its members the same slice text, under a different
file name; the 32 extra parses cost 232 s, and their searches and checks run
again too. Fragments carry 60,471 declaration definitions, of which 1,128
are distinct (219 MB against 5.7 MB). The parser's compiler is opened per
parse (41 s) and builds the project's program for imported modules (96 s).

**Measured — after a first experiment** (this branch, uncommitted, the
parses of `moduleFunction`, `inertRead` and `expandMapped` in one process,
store off): parse CPU 6.26 + 3.89 + 1.71 s → 3.22 + 1.82 + 0.91 s, with
§3.1–3.3 applied; of the compiler's queries, 122,494 of 151,228 asked a
snapshot again what it had answered.

**Cited — the Fragment names the resolution file.** The client's own
declarations are identified by the resolution file's absolute path
(`moduleIds`, `tools/declaration-graph.mts`): the Fragment of the
`expandMapped` slice names `…/tools/slice-type-term-expandMapped.mts` as the
module of `TermScope`, `FunctionTerm` and `RestPositions`.

**Measured — the verifier's preparation** (sampled, 2026-10-24): lowering
the declaration document to equations (`EquationLowering`,
`Equations/Core.lean`) takes 0.75 s of `moduleFunction`'s search and 0.81 s
of its check (38% of the check), and 1.27 s at the synthetic width 136; the
claims are decoded a second time while freezing plans (about 0.3 s). Search
and check each prepare their input from the documents.

## 2. The model

The idea is taken from [SKStore](../REFERENCES.md#skstore): a store of
directories, each entry a value under a key; *input* directories written by
the outside world; *derived* directories whose entries are computed from
others; and a computation's dependencies being exactly what it read. A
*lazy* directory computes an entry when it is asked for, records the
entry's read set, and serves the entry again while that read set is
unchanged. A lazy computation that reads another lazy entry depends on what
that entry read.

The front end is such a computation. Its inputs are the file system (each
answer an operation gives at a path) and the named inputs of a request (a
snapshot's bytes, a project, a resolution file, the active family
descriptions). Every piece of its work is a derived entry: a function of
named inputs and of the file-system answers it read. TScert already has
three kinds of derived entry, each a lazy directory with a read set:

- **Store entries** (`pipeline/stages.mts`, `pipeline/stage-store.mts`): an
  observed stage's entry is keyed by its pre-key (its named inputs) and its
  observations (its read set); a later invocation with the same pre-key
  replays an entry whose observations hold now. An observed stage invoked
  while another runs is a nested lazy read: executed, its answers are noted
  in every record being made (`note`, `tools/files.mts`), so the enclosing
  stage's read set holds them; replayed, its observations are made again
  while the enclosing record is being made, with the same effect.
- **Process caches** (`remembered`, `tools/files.mts`): a value with the
  observations it was computed from, made again at its first use in an
  attempt and noted in every record that uses it.
- **Ledgers** (`withLedger`, `tools/files.mts`): the read set of a long-lived
  computation, a retained compiler, noted in every record that uses it.

The design adds no new kind of entry. Each repeated cost becomes one of
these, at the lifetime its inputs fix:

| Lifetime | Entry | Key | Read set |
| --- | --- | --- | --- |
| an attempt | a file-system answer | operation and path | itself |
| a compiler snapshot | a query's answer | method and parameters | the compiler's ledger or attempt |
| a process | a resolution | specifier and parent | its observations (`remembered`) |
| a process | a retained compiler | its compatibility descriptor | its ledger |
| the store | a parse | its pre-key | its observations |
| the store | an imported module's lowering | its pre-key | its observations |
| a session | a declaration's collection | its identity and the run's selection | the session's ledger |

Every entry is lazy: computed when a computation first asks for it, as the
pipeline asks for a slice's check. Eager directories (entries recomputed
when an input changes, and propagated to their readers) fit a system that is
told of changes; the file system tells the front end nothing, so validity is
established when an entry is used, by making its read set again.

**Not taken from SKStore, and why.**

- *Push invalidation.* SKStore marks readers dirty when an input changes. The
  file system announces no change; a read set made again at use is the only
  validity the front end can establish, and the store already does that.
- *Dependencies on entries.* SKStore records that a reader read entry `k`,
  and versions entries. Here a reader's read set holds the file-system
  answers its nested entries read, flattened. One validation per entry costs
  what a version check would save, and the flattening keeps one form of
  observation for every stage.
- *Transactions and garbage collection.* The store publishes immutable
  entries by atomic rename and evicts approximately; a reader treats a
  missing entry as a miss. Nothing here needs more.
- *A general directory abstraction.* The three kinds of entry above keep the
  code they have; the design extends their uses, not their number.

## 3. What each repeated cost becomes

### 3.1 File-system answers, once per attempt

**Entry.** Within an attempt (the outermost observed stage's record being
made, `observedNoting`), the operations `kind`, `real`, `dirents` and
`entries` the front end makes at a path for itself or for a compiler answer
what they answered first in the attempt, and the answer is noted again in
every record being made. Three kinds of read stay fresh: a read outside
every record (a ledger's validation suspends them, `validateLedger`); a
read standing for one of Node's (a Node-origin observation: the probes
before and after Node's resolution, the loader's reads), so that their
agreement and the process's first answers compare what the file system
answers, never an earlier answer; and `read`, whose bytes are what the
caller uses. A fresh read is not kept for a later one, so a front-end answer
is never served for a Node-origin read, nor the reverse.

**Trust.** The store assumes the file system stable while a stage reads it
(STAGE-STORE.md, retained declaration sessions); this entry makes the
assumption operative for the front end's own reads: the attempt's
computation is a function of exactly the answers its record holds. A path
whose answer changes between two of the front end's reads in one attempt
was reported as `answered differently within the stage`, making the attempt
incomplete; with the entry the second read answers the first answer. That
detection caught a change only at a path read twice; the end-of-stage
ledger validation and the replay's validation remain the checks of
stability, and Node's reads keep theirs (fresh probes, first answers). No
conjecture is added; one partial detection of instability is given up, a
cost stated in the trust row.

### 3.2 Resolutions, once per process, validated per attempt

**Entry.** `nodeResolve(specifier, parent)` is a process cache
(`remembered`, keyed by both): computed once with its two observations and
Node's resolution, then, at its first use in each attempt, its observations
made again, and noted in every record using it. Node's resolver is not
asked again, so its own cache cannot answer otherwise.

**Trust.** None new: `remembered` is the mechanism the guard tables and
declaration origins use. A Node-origin answer is compared with the
process's first answer when made again, as now.

### 3.3 Compiler questions, once per snapshot

**Entry.** A query of a snapshot, a request of an audited list of methods
(the checker's, program's and symbol's reads the front end makes, each
naming the snapshot it reads; the list is in `tools/compiler-channel.mts`),
is answered from the client's record of that snapshot's earlier answer to
the same method and parameters, as text; the snapshot's answers go with its
`release`. Every other request (a snapshot's update or release, a
configuration's parse, a method off the list) goes to the compiler. The
entry lives in the channel, under every call site.

**Read set.** An answer served from the entry is a read of the compiler's
state, as every request is; §3.5's rule gives every request, served or
asked, the compiler's ledger as part of its read set.

**Trust.** It adds one conjecture, *query omission*: for a query on the
list asked of an unreleased snapshot, (a) asking it again answers the text
it answered first, and (b) omitting the repeated request changes no answer
the compiler gives afterwards to any request, of that snapshot or another,
failures included, over the compiler's lifetime. Determinism of the
compiler's state (STAGE-STORE.md, observed stages) gives neither: a query
may load a dependency lazily, which a later request then finds loaded. Its
tests compare whole parses, Fragments and ordered diagnostics byte for byte,
with the entry and without it, in the orders the session controls use (§5).

### 3.4 An imported module's lowering, once per store

**Entry.** A new observed stage, `module`: the lowering of one imported
program module as a run of that module alone lowers it (`parseModules`,
`tools/fragment-parse.mts`). Its pre-key is the module's absolute path, its
identity in the importer's documents (`location`), the named project, the
active family descriptions and the run's tag selection of each host family
(HOST-FAMILIES.md, residuals), canonically ordered; its read set is its
observations. Its value is the module's entry as text (`ModuleAst`) and the
modules it imports, or the gate's refusal (the module left out, as now); a
tool failure is no value. The parse invokes it once per module it reaches;
executed, the stage opens a parser compiler of its own and releases it, and
collects in the declaration session; replayed, it opens nothing.

The parse's pre-key is unchanged. Its observations are a conservative read
set: the answers its own lowering read, and for each module the read set of
the module's entry, executed or made again on replay (§2), with the answers
of candidates whose validation failed. A replayed module entry's read set is
the one its own execution recorded, a session's ledger of another worker
included. A parse entry is therefore keyed by at least every answer its
result depends on, and may replay less often than before, never wrongly.

**Trust.** The module's lowering is specified as "a run of that module alone":
the stage makes it one, in a parser compiler of its own at the module's
directory. Today it shares the importer's parser compiler (its working
directory, the importer's open document, the programs it built); the
change adds the obligation *module isolation*: a module lowered in a parser
compiler of its own is the module lowered in the importer's, byte for byte.
It is tested by the Fragments of every pipeline case, parsed before the
change and after it, store off (§5). Its collection's fidelity is the
session's. New in the trust row: a stored module entry is the parser's own
lowering of exactly the inputs its key binds, as for the parse. The
Fragment assembled from replayed entries is the one assembled from executed
lowerings: the parse splices each module's text into its `modules` list in
the order it reaches them, the bytes of `JSON.stringify` of the same value,
and checks well-formed strings in the same document order (the module's
value carries its own check's result).

### 3.5 Compilers, each with its read set

**Rule.** A record that uses a compiler holds every answer that compiler
was given over its lifetime. Every front-end compiler has one ledger, kept
by its channel (`tools/compiler-channel.mts`): a retained declaration
session's is its session's ledger, as now; a compiler opened for one parse,
one module lowering or one automatically selected collection has a ledger
of its own. Before every request of a compiler, asked or served from §3.3's
entry, the channel notes the compiler's ledger in each record being made
that does not hold it yet (its answers, incompleteness and inconsistency,
as `importLedger` does), and the request runs with the ledger kept
(`withLedger`), so the answers it is given reach the ledger and every
record being made.

*Growth.* Records are made in a stack: every record that holds a ledger and
can still use the compiler is being made, so every later answer, and every
later incompleteness or inconsistency, reaches it while it is made (`note`,
`unobservable`, `inconsistent` act on every record being made). Noting a
ledger once per record (`holding`) is therefore complete: a ledger grows
only during a request, and every open holder sees the growth. A record begun
after a request, a nested stage's or a process cache's, is noted the
ledger before its own first request of the compiler.

**The parser compiler, retained: measured, then decided.** A retained parser
compiler would be a session of the declaration session's discipline: a
ledger validated before each reuse and before each publication; a base
state restored and checked (no open document, no project, an empty
overlay, the compiler told of every overlay path that changed); and
compatibility by installation, families and working directory. The
parser's compiler opens at its snapshot's directory, which differs per
source; a retained one needs either one directory for every parse (the
store's source root) with *directory independence* of the parse as a
further conjecture, or reuse only between parses of one directory, which
the census never makes. After §3.4 the parser's compiler opens once per
parse for the main file alone (measured cost before §3.4: about 90 ms of a
parse). It is built only if, measured after §3.4, its saving exceeds its
ledger's validation per parse and is worth the conjecture (net savings
against maintenance and trust); otherwise this section records the
measurement and the parser keeps a fresh compiler per parse.

**One compiler for parsing and collection: not taken.** The snapshot lives
in the store's source directory, outside the named project, so the
declaration session would hold a second project; and a project-less check
has no session. The parser keeps a compiler of its own.

### 3.6 Duplicate slices: one question asked once

**Key.** The parse key keeps binding the resolution file's path. The Fragment
names it (§1, cited), and the compiler reads the file by that name; a parse
key binding only its directory would rest on a new conjecture, that
TypeScript's answers for two files of one directory with the same bytes
differ only in their names (an `include` pattern, a `files` list or another
file's import distinguishes them). It is no weakening worth its gain.

**Entry.** The census (`dev/census.mts`, outside every key) writes one slice
file per distinct slice text, named by the first function of its module
holding that text, and checks it once; each function holding the text
reports that check's outcome. Its records keep one row per function, its
invocations the shared check's. The parse, search and check of a group run
once.

### 3.7 A declaration's collection, once per session

**Entry.** Within a declaration session, the collection of one type
declaration outside the client (`collect`, `tools/declaration-graph.mts`)
is an entry keyed by the declaration's identity, the run's tag selection
and the guard promises the run reads. It holds the declaration's definition
with every identity in it written stably (a declaration of the client by a
client marker, every other by its project-relative identity, `moduleIds`),
and the log of its effects on the document in order: each symbol and
private name it names (by identity), each diagnostic it reads, each
declaration it queues. A collection reaching the declaration instantiates
the identities through its own `moduleIds` and replays the log through its
own context (symbol indices, diagnostics, the visited set and the queue),
in the order a fresh collection makes the same calls, so the document's
indices and order are a fresh collection's. An entry whose computation
reads the client (an identity of the client, a computed form over it) is
not kept. Its read set is the session's ledger; the entries go with the
session.

**Scope.** The store is not used: an entry's read set would be the
session's whole ledger, and its value a serialization of definitions and
logs with a decoder of its own, for reuse across workers that each compute
it once. The client's own declarations and the per-use work (values, checks
at the client's spans) stay per collection.

**Gate.** This step changes the most trusted code and saves at most what
`collect` costs: 31% of a collection in the 3-slice profile after §3.1–3.3.
It is built if, measured after §3.1–3.6, its saving over the census exceeds
its maintenance and trust cost (the code it adds to the trusted collection,
and the conjecture below); otherwise this section records the measurement.

**Trust.** It adds a conjecture of the same kind as session fidelity: *a
declaration's definition and effect log, computed in a session whose ledger
holds, instantiated in a later collection of the session, are what that
collection computes for the declaration.* Tested as §5 tests sessions.

### 3.8 The verifier's preparation

**Indexed tables.** Equation lowering keeps its pending jobs in a list it
scans by head (`tryEnsure`, `jobs.find?`), appends each new job at its end
(`alloc`) and builds rows by list appends (`groundRows`): a superlinear
cost, inferred, to be confirmed by a profile before the change. The jobs
become a queue in allocation order with an index by head: `drain` takes the
oldest job still pending, `tryEnsure` takes a head's job out of the queue,
and the `processing` check is unchanged, so jobs run in exactly the order
they run now and every head is allocated at the same index. Rows become
arrays where they are appended. The claims document is decoded once and the
decoded form reused while freezing plans. The obligation is equality of the
lowered equations, head by head, before and after. It is tested directly:
the preparation of every pipeline case (its equation table, head by head,
with its annotations, values, generics and units, or its refusal), printed
by the verifier's preparation mode, is the same text before and after; and
by the suite's outcomes and evidence documents, byte for byte (§5). A case
whose base class is declared after its subclass makes `tryEnsure` take a
later head's job before `drain` reaches it. Being `partial`, these
definitions carry no proof that would show it.

**Shared declarations lowered once, carried from search to check: not
taken.** A lowered equation table is the meaning of the source's
declarations (`EquationLowering`, trusted in what it states). Two forms of
reuse were weighed:

- *Through the store*, a stored preparation read by the check (or shared
  across slices): a new trusted wire format and its decoder, and the check's
  premise moved from the Fragment to that document, for at most the
  lowering's cost after indexing.
- *In one process*, a combined invocation that prepares once from the bound
  inputs, searches, then checks the evidence it produced against the same
  preparation (by `checkJson`'s definition as preparation followed by
  checking, an equivalence kept by construction). It needs no wire format;
  it merges the search and check stages into one invocation, keyed and
  replayed together, so a check is no longer replayed apart from its search.
  Measured (6a3a864 census): the check stage costs 52 s over 170 checks,
  its preparation about 40% of the check in `moduleFunction`, so the
  combined invocation saves at most about 20 s of the census.

Neither saving exceeds its cost now. The check prepares its input from the
documents its key binds and re-establishes nothing of the search's output.
Reconsidered with the census's numbers after indexing.

## 4. Keys

- *Parse:* unchanged (source bytes, snapshot path, resolution file, project,
  families; observations, the module stages' included).
- *Module:* stage `module`; inputs `module` (absolute path), `location`,
  `project` (or empty), `families` (JSON of the active descriptions),
  `selection` (each family's marker with its sorted tag values); observed,
  with the compiler's identity; its observations.
- *Diagnostics:* unchanged.
- *Process stages:* unchanged.

No key loses an input. The module stage is a new stage name in
`stageNames` (`pipeline/stage-execution.mts`) and a row of the stage table
(STAGE-STORE.md).

## 5. Tests

- *Byte identity, fresh against shared.* For the session controls' fixture
  and the census's sample slices: Fragments and ordered diagnostics with
  sharing (attempt answers, query answers, module entries replayed and
  executed, a reused parser session) equal to those of fresh compilers with
  the store off, in forward, reverse and A–B–A orders, refusals included
  (`tests/session-reuse.mts`).
- *Module entries.* A module entry replays opening no compiler; a changed
  module, project file or family selection misses it; the parse's entry
  holds the module's observations, executed and replayed (a change to a file
  only the module read refuses the parse's entry); a refused module is left
  out in both.
- *Query answers.* A repeated query of a snapshot answers from the entry; a
  released snapshot's answers are gone; a query of another snapshot asks the
  compiler.
- *Attempt answers.* Within an attempt a repeated operation notes its answer
  in a nested record begun after the first; a ledger's validation reads
  afresh; a change between attempts is seen by the next.
- *Parser session.* As the declaration session's controls: reuse, replacement
  on another installation or families, a changed ledger answer, an unclean
  restoration, a tool failure, and CPU accounting.
- *Census.* Outcomes per function equal before and after each step; any
  change reported with its cause.
- *Compiler ledgers.* With a compiler opened for one stage: a nested record
  begun after a request is noted the compiler's ledger before its first
  request, asked or served; a record that holds the ledger, after the
  ledger grows, receives the growth and is not noted it twice; an
  incompleteness of the compiler reaches every holder.
- *Verifier.* Every pipeline case's preparation printed and equal before and
  after the indexing, refusals included; its outcome and the evidence
  documents of the suite equal too.

## 6. Expected costs

Estimates (conjectured) from the 6a3a864 census's 932 s of parse and the
3-slice experiment; each step's measurement replaces its line.

| Step | Census parse |
| --- | ---: |
| §3.1–3.3 attempt answers, resolutions, query answers | 932 → about 500 s |
| §3.4 module entries | → about 330 s |
| §3.6 duplicate slices | → about 240 s; their search and check too |
| §3.5 parser session | → about 210 s |
| §3.7 declaration entries, if built | → about 150 s |

Per phase: collection loses its repeated file-system answers and queries
(§3.1–3.3); imported modules' collection and program cost about once per
module per census (§3.4); the parser's opening once per worker (§3.5);
ledger validation stays per use. The verifier's preparation: lowering's
0.75–0.81 s per tools slice, expected to fall with the table (measured).

A step whose measurement misses its expectation is investigated, and the
design revised, before the next step.

Each step is measured on the sample slices (`keyOf`, `holdsAny`,
`expandMapped`, `moduleFunction`, the 1,301-line `tryStmt`, `expr`) and by
one cold census in a fresh store; the verifier's part on the search and
check of `moduleFunction`, `inertRead`, `resolve` and `collect`.

## 7. Migration

Each step lands whole, its documents and trust rows in the same commit.
Formats keep one shape: the parse's stored value is unchanged; the module
stage is a new stage with its own value; nothing reads an older entry of a
changed code identity, which every keyed code change misses already. The
store needs no cleaning: a new code identity misses every old entry.

## 8. Trust changes, summarized

- §3.1: none added (the store's stability assumption, made operative for
  the front end's own reads); one partial in-stage detection given up.
- §3.2: none.
- §3.3: query omission (conjectured; tested).
- §3.4: module isolation (conjectured; tested over every pipeline case), and
  a stored module entry is the parser's own lowering of exactly the inputs
  its key binds (store binding, as for the parse).
- §3.5: every compiler's ledger held by every record using it (a rule, by
  construction); if the parser session is built, its fidelity and directory
  independence (conjectured; tested as the declaration session's).
- §3.7, if built: declaration-entry fidelity within a session (conjectured;
  tested).
- §3.8: none.

The trust rows of DESIGN.md (the replayed parse, retained sessions) are
updated in the commit of each step.
