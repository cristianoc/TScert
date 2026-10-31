# Working in TScert

An independent verifier for type claims about TypeScript programs: a calculus
with a semantic model and soundness proofs in Lean, a checker that validates
certificates, and a pipeline that parses a TypeScript source, has the OCaml
producer propose its claims, and asks whether they are derivable.
[README.md](README.md) is the entry point; [DESIGN.md](docs/DESIGN.md) holds the
decisions. Everything below is what an agent needs to change things here
without breaking the suite's shape.

## Commands

```sh
make help        # every target
make test        # build, then the fast checks and the controls, replayed from the store
make suite       # build, then the pipeline cases
make cases P=x   # the pipeline cases whose file names contain x
make check FILE=f.ts [PROJECT=dir]  # one source file through the pipeline
make lowering FILE=f.ts [FN=name]   # the program graph a source lowers to
make semantic-diff REV=rev          # render the commit records of a commit or range
make build       # build-lean, build-producer and build-runner: the Lean verifier, the OCaml producer and the stage runner
make setup       # the node dependencies
make clean-store # remove stage entries, timeout observations and the source snapshots no running process holds
make census [DIR=tools] [FILES=…] [FUNCTIONS=…] [SHARD=i/n]  # the census of a directory's functions
```

### The stage store

Every stage and every operation of a control replays from
[the stage store](docs/STAGE-STORE.md) by content, through
[one mechanism](pipeline/stages.mts); the parse and TypeScript's diagnostics
replay as [observed stages](docs/STAGE-STORE.md#observed-stages) on macOS.

- The front end reads the file system only through `tools/files.mts`, and
  opens its compiler only through `openFrontEndCompiler`
  (`tools/compiler-channel.mts`); `tests/observed-stages.mts --reads`, a fast
  check, refuses a module of the stages' code that imports a file-system,
  module or process API itself.
- A key covers every `.mts` file directly in `pipeline/` (and in `tools/` for
  an in-process stage) by content, but the files `unkeyed` names
  (`pipeline/stage-execution.mts`). Editing an unkeyed file replays every
  entry; editing or adding any other file there misses every entry it keys.
  A new file that only orchestrates or presents goes on `unkeyed`, with its
  role stated in [keys](docs/STAGE-STORE.md#keys), in the same commit.
- `TSCERT_STAGE_STORE=<dir>` selects the store, by default
  `~/.cache/tscert/stages`, shared by every checkout and worktree; `off`
  executes every stage. A branch uses the default store; an agent testing
  the store itself names one under `$TMPDIR`. The store keeps itself within
  `TSCERT_STORE_BUDGET` (15 GiB by default), the case runner, the census
  and the controls starting a background pass that evicts the least
  recently used entries ([location and size](docs/STAGE-STORE.md#location-and-size));
  `make clean-store` removes every entry and timeout observation.
- Each process stage is killed after 60 s, and a control's operation after
  30 s unless the control states another limit;
  `TSCERT_STEP_LIMIT=<seconds>` sets a stage's limit. A timeout is recorded with its limit and reported
  again at that limit or a smaller one; `TSCERT_RETRY_TIMEOUTS=1` executes
  it again at the same limit.
- A run's directory holds `invocations.jsonl`, each stage invocation's
  attempt: its stage key, limit, outcome and elapsed time.

### Iterating: run what the change touches

The full battery is for deep changes. While iterating, run the narrowest tier
that covers what changed, and the wider tier once before committing:

| Changed | While iterating | Before committing |
| --- | --- | --- |
| OCaml producer (`ocaml-producer/*.ml`) | `dune build --root ocaml-producer`, then `node pipeline/run-cases.mts <pattern>` (cases whose file names contain the pattern; about a second for a handful) | `make suite`, then `make test` (the controls: forged documents and claims no case can make) |
| One source file | `node pipeline/verify-source.mts <file.ts> [--project dir]` | — |
| Lean | `(cd lean && lake build)`, then `run-cases.mts` for the affected cases | `make suite`, then `make test` |
| Parser, Fragment or SourceClaims wire, shared tools | `(cd tools && npx tsc -p tsconfig.json)`, `node tests/json-field-names.mts` (instant: TypeScript, Lean and OCaml use the same JSON field names), then `run-cases.mts` | `make suite`, then `make test` |

`run-cases.mts` with no pattern runs every case (26 s on 12 cores, measured
2026-10-16) and is `make suite` after its build. Cases run in one worker
process per core, each keeping its TypeScript compiler between cases;
progress goes to standard error.

The wider tier runs once for each change of producer, Lean, parser or
shared-tool code. A later edit of cases, examples or docs alone reruns only
the cases it touches (`run-cases.mts <pattern>`), and a doc edit runs
`node tests/docs.mts`. A case that fails on a timeout while the machine is
loaded is rerun by its pattern, not with the whole suite.

### Measuring coverage: once, on main

The census of the front end's own functions (each top-level function of
`tools/` sliced and run through the pipeline) runs once on main, after a
merge, and its movement is recorded then. A branch runs no census, over
`tools/` or over a file. To show a change does what it is for, it runs the
slice of the function the change targets and one slice depending on it,
before and after (`make census FILES=f.mts FUNCTIONS=fn,other`).

### Choosing the gap cases to work on

A round of this work runs in the order of the
[gap-round skill](.claude/skills/gap-round/SKILL.md), its agents briefed by
[its brief](.claude/skills/gap-round/brief.md).
Work on coverage follows two steps, both from the census of main
(`make census`), whose record keeps each refused slice's first refusal:

1. **Where proofs fail:** `node dev/census.mts refusals <record>` groups
   the refused functions by the blocker their first refusal names, with
   the statements each group blocks. Every reason
   that names one construct counts, whatever stage refuses it, the
   producer's included; a reason that may stand for several causes (a
   failed search, an expression with no claimed type) is first split into
   its causes by the functions it meets. A reason blocking much code that
   no pipeline case shows gets a case example: the smallest source with
   that refusal, its header naming the census functions it stands for.
2. **Priority:** the gap cases are worked in the order of the reasons they
   show, by the code those block; each is answered by the routes of
   [deciding what a refusal calls for](docs/SOURCE-REWRITES.md#deciding-what-a-refusal-of-tscerts-code-calls-for).
   Before a route is chosen, a reason's sites are split by whether
   TScert's own code discards what it already knew (a parsed JSON value
   typed `unknown`): those sites are repaired in the code. A case blocked
   by external code no contract describes yet is answered by describing
   it, in whatever shape it needs; the trust that description states is
   reviewed by the owner before the merge, not waited on. An assumption
   that standard objects are not tampered with (no method of a Node or
   JavaScript built-in prototype or object replaced, or wrapped in a
   getter, by any code) is approved by this policy; any other kind goes to
   the owner.
   The [gap-priorities deep dive](docs/deep-dives/gap-priorities) presents
   the ranking and each case, closed or open; after the census on main
   that follows a batch of merged cases, it is rebuilt from that census and
   reaches the owner marked since the version last approved
   ([a revised deck](docs/STYLE.md#a-revised-deck)).

`make census` limits each stage to 300 s unless `TSCERT_STEP_LIMIT` is
set, so a slow search reports the outcome it reaches rather than a
timeout; the pipeline cases keep the 60 s default.

[`dev/census.mts`](dev/census.mts) writes a census record per run (each
slice's outcome and its stage invocations with their timings) and prints
its path. `SHARD=i/n` runs every n-th distinct slice file from the i-th, so n processes
or agents split a census and share the stage store; a later run replays
what an earlier one computed. `node dev/census.mts report <before>
<after>` compares two censuses, each one record or its shards' records
separated by commas: slices gained and lost, timeouts, changed outcomes,
each stage's time and the movement of
[statement coverage](docs/DESIGN.md#statement-coverage). `report <record>`
prints a census's verified statement coverage per directory and file
(`--per-function` adds each function), and `coverage <record>
[--sources checkout|commit]` computes it for a record from the sources of
the record's commit or of the checkout, running no slice. A census rerun with a longer `TSCERT_STEP_LIMIT`
executes the stages that timed out again and replays the finished ones.

A branch is ready to merge when `make test` and
`make suite` pass and its review is done, and reports as soon as its suites
pass. A small, local fix whose output is unchanged (an untrusted
search's speed, a diagnostic's wording) merges on green suites without a
further review round; a new rule or a change of trust is reviewed before it
merges.

### Working in a separate git worktree

A new worktree has an empty `lean/.lake`, and its first
`lake build` compiles every module from scratch: 3.5–5 minutes on 12
cores. Clone the main checkout's cache into it instead, before the first
build:

```sh
cp -c -R <main checkout>/lean/.lake lean/.lake
rm lean/.lake/build/bin/verifier
(cd lean && lake build verifier)
```

On APFS `cp -c` copies on write: it takes a fraction of a second and no disk
until files change. Lake decides what to rebuild from file contents, not
timestamps or paths, so the clone stays valid in the new directory. A build
at the same commit then rebuilds nothing, and an edit rebuilds only the
changed module and its dependents. The link step is the exception: the
copied `verifier.rsp` names the main checkout's object files by absolute
path, and `pipeline/evidence-mutations.mts` relinks a mutated verifier from
it, so removing the copied executable makes Lake relink it (about 1 s) from
the worktree's own objects. The saving is complete when the main
checkout's cache is built at or near the worktree's commit; otherwise Lake
rebuilds just the modules that differ. Each worktree keeps its own `.lake`,
so builds in different worktrees may run in parallel. Dune restores OCaml
builds from its shared cache. Each `node_modules` directory is copied from the
main checkout with `cp -c -R` (never committed): the root's, `tools/`'s and
every `pipeline/*/` one, `pipeline/library-project/node_modules` included. A
symbolic link resolves type declarations from the main checkout's path, and
the cases reading `@types/node` then fail.

`make suite` includes the pipeline cases, including those importing from
`pipeline/imports-project/` and `pipeline/library-project/`. Install OCaml and
Dune as described in [the producer guide](ocaml-producer/README.md#try-it)
before running it.

One file end to end, with `$F` a repository-relative path:

```sh
node pipeline/verify-source.mts $F
```

It prints the outcome and the directory holding what the run wrote: the
source snapshot, the parser's `fragment.json`, the producer's `claims.json`
and the verifier's `evidence.json`.

A refusal of TScert's own code is answered by the first of the seven routes
[source rewrites](docs/SOURCE-REWRITES.md#deciding-what-a-refusal-of-tscerts-code-calls-for)
states that establishes the obligation at acceptable cost: support, a runtime
check, a repair, avoidance, a host boundary, a trusted unit (owner-approved,
never a fallback) or a proof. A case is a negative case only where its program
is unsafe, shown under Node. A repair, an avoidance or a
host boundary is recorded there in the same commit, with what its kind
requires.

## Which tests to keep

The end-to-end pipeline cases are the primary signal: a source file through
the parser, the OCaml producer and Lean (`pipeline/cases.mts`, run by
`run-cases.mts`). They exercise the unproved parts together (parser,
extraction, producer, wire), and what Lean proves needs no test.

- **Prefer a pipeline case.** A new feature's test is a source file with its
  expected outcome, positive and negative, not a unit test of an
  intermediate step.
- **Research tests are temporary.** Tests written while working a feature out
  (a Lean `#guard` on a hand-built graph, a probe of one tool) are useful
  while researching it. Once a pipeline case covers the behaviour, retire
  them in the same or the next commit.
- **Keep a test only for what the pipeline cannot show:** a refusal no source
  can reach (forged evidence, a tampered declaration), a boundary of a
  trusted input (the `ArrayProto` overlay), or a speed-critical check.
- **Remove what adds no signal.** A test a proof already covers, or one that
  repeats another's inputs through the same path, goes. Before removing a
  forged-claim test, check it does not test extraction: which program point a
  claim is attached to is unproved.

## The suite's shape, and the rules that keep it

`make test` builds (a no-op when nothing changed), then runs `test-all.sh`:
the fast checks and the controls (`pipeline/test.mts`). `make suite` builds,
then runs the pipeline cases (`pipeline/run-cases.mts`). Three rules decide
where a check goes.

- **Suites start together.** A suite is `run_test "Name" command args…`; its
  output is buffered and reported in order, and a failure is counted, never
  fatal.
- **A case is a source with its expected outcome; anything else is a
  control.** A check of a source through the pipeline is a case of
  `pipeline/cases.mts`. A check of the verifier, the producer or the
  pipeline on an input no case makes (a forged document, a mutation, an
  injected failure, a family override) is a control of `pipeline/test.mts`;
  a check running no stage is a suite of `test-all.sh`.
- **Controls replay like stages.** Each control block of `pipeline/test.mts`
  registers with `control(…)` (`mutationControl(…)` where it runs the
  mutation verifier); a pool of control processes, one per core, runs them.
  Every operation a control runs goes through `tested` (`pipeline/stages.mts`)
  and replays from the store when its executable, inputs and environment are
  unchanged ([controls](docs/STAGE-STORE.md#controls)). A control is
  independent of the others: it reads its cases' artifacts through
  `run(…)`, the case checked through the pipeline in its own process, and
  states its own family overrides. The suite reports the controls' wall
  time and how many of their operations executed and replayed. Controls of
  the store itself (`tests/observed-stages.mts`, the replay control) name
  fresh stores and execute every time.

## What a result means

### Acceptance/soundness invariant

The verifier's successful CLI outcome must imply the modeled safety property
for every extracted function. Preserve this by construction:

- The acceptance path consumes the complete `FunctionPlan` sum through one
  exhaustive conversion to `CertifiedPlan`. It must never use `filterMap`, an
  `Option`, or a projection that can discard a plan variant.
- A new plan constructor must make that conversion fail to compile. It may
  become a certified constructor only with a checker and a theorem connecting
  its successful check to the semantic property. Until then it is a located
  gap, never `verified`.
- Keep one headline theorem, `SourceClaimJson.checkJson_safe`, whose
  premise is the exact CLI success condition and whose conclusion gives safety
  for every accepted function. A theorem about a retained subset, decoded
  bundle, or Boolean alone is not an acceptance soundness theorem.
- The axiom check checks how a theorem was proved, not whether it proves the
  required statement. Review the theorem's premise and conclusion whenever the
  accepted plan type or CLI path changes.
- Search output, direct-check success and compiled ground consequences are
  intermediate artifacts. The runner and diagnostics must not label them verified
  before the corresponding plan reaches `CertifiedPlan`.

## Source and host soundness boundaries

### Designs start from an existing mechanism

A design draft (`docs/drafts/`) opens with a section **The existing
mechanism this extends**, citing the document that owns it (for a fact a
construct relies on across code, [footprints](docs/FOOTPRINTS.md): the
fact, its stable operations, the checked contract, the construct's rule).
[The general mechanisms](docs/DESIGN.md#general-mechanisms) lists each
concern's mechanism. Where no mechanism fits, that section lists the mechanisms considered and
why each falls short; no new machinery is proposed before it is written.
Every review of a design or of a new rule asks first: is this an instance
of an existing mechanism, and which; what does it duplicate?

### Engineering trade-offs

[Utility justifies complexity](docs/DESIGN.md#principles): an explicit,
enforced restriction is an acceptable decision, chosen by the behaviour it
excludes, not by a particular failing example. Document it in
SOURCE-FRAGMENT.md, enforce it at the source/semantic boundary, state the
same requirement for external code where relevant, and keep a small control
showing the excluded behaviour cannot silently enter the admitted fragment.
A restriction simplifies the language, not the meaning of an accepted
program: never erase a contract or ignore a possible runtime action. A
motivating ordinary program that stays blocked is open work in WORK.md.

The calculus theorem does not prove that a source annotation was interpreted
faithfully or that a native library meets its assumed contract. These are
separate review obligations, even when every Lean proof and suite passes.

- **Never erase an unsupported contract.** Source annotation lowering either
  represents the whole contract or refuses it. An unsupported method, a failed
  expansion, or an exhausted search/colour budget must not become `top`, lose
  a field, or lose a bound. An opaque type is not `unknown`: hiding its
  representation does not discharge its introduction obligation. The same
  declaration occurs in inputs, outputs, and invariant storage; an
  over-approximation safe for reading is not safe for producing a value.
- **Native declarations are specifications to audit, not evidence.** Review
  every callback (including implicit conversion, iteration and thenable
  callbacks, constructor lookup and `Symbol.species`), its actual arguments,
  alias mutation, and whether lengths or
  keys are captured before callbacks run. A readonly alias does not prevent
  mutation through another alias. Establish result invariants after all such
  effects; density at entry does not imply density of `map`'s result. Callback
  effects do not constrain other native entry points. Check result construction
  as well as traversal. The semantics assumes ordinary array
  construction, also of external code: no own array `constructor`, and stable
  standard constructor/species behavior. Preserve the formal own-key exclusion
  through all array/record views and reject source operations violating it.
  Custom species are outside the admitted language; their full modeling is not
  a prerequisite for callback-effect work. Never widen this assumption silently.
  Standard array conversion additionally excludes own `toString`, `join` and
  `Symbol.toPrimitive` and assumes their standard prototype behavior, also of
  external code. Keep these key bounds and the prototype's undefined hook view:
  numeric elements alone do not justify implicit conversion. The recursive
  conversion contract and the rationale for excluding custom hooks live in
  [prototype contracts](docs/SOURCE-CONTRACTS.md#prototype-contracts).
- **Test the unproved boundary independently.** A producer-side refusal needs
  a verifier test bypassing that producer when annotation interpretation is
  involved. For native-contract repairs, execute the actual negative source
  fixture under Node as well as refusing it in the pipeline. This is a small
  contract counterexample, not a test of a proved Lean typing rule.
- **Keep dependencies exact.** Collect only intrinsics a source uses; do not
  load all trusted contracts because one is needed. Dependency collection may
  avoid unused declarations, but may not discard members of a collected type.
- **Coverage losses are results.** Preserve motivating sources; mark a case
  blocked by an earlier unsupported contract as a gap, not as a passing
  negative control for the later obligation. Report lost coverage
  explicitly. Changing an expected result requires inspecting its cause;
  passing tests after reclassification does not close the corresponding goal.

Array presence is separate from read/write capability
([density belongs to a contract](docs/DESIGN.md#lasting-decisions)). Never
special-case `unknown[]` by spelling; never let an existing writable store
location change its contract; preserve the presence mode through every
graph/claim mapping, and distinguish array-store metadata from argument
packs, which hold values and have no holes.

For inferred callable effects, follow the
[elaboration/certification boundary](docs/SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification).
Annotation translation must not strengthen an ordinary arrow. Producer inference
proposes a qualified signature; definition evidence must prove both safety and
the effect before application consumes it. Never recognize callback syntax at
native call sites as a substitute for that proof. Audit every signature mapping,
substitution, overload and certificate path for the effect field; exhaustive
constructor matching does not detect a discarded field. Qualified claims need
located failures and forged-evidence controls, and imported effects require an
explicit checked contract or documented external assumption.
The current effect guarantees preservation only on normal return. Do not carry
it onto a call's exceptional edge or infer preservation for a caller that catches
the exception without checking its handler against the changed heap.

Agreement between the OCaml producer and the Lean checker does not catch a
specification mistake they share, such as reading an unsupported generic method
as `unknown`, or copying a native array contract from TypeScript's signature
without accounting for reentrancy and coercion. Keep the refusals and controls
that guard these when extending the fragment; do not gain acceptance by
increasing trust silently.

## Conventions

- Formatting: everything is prettier-formatted (`make fmt` at the root).
- Every module the node side runs is `.mts`, and `tools/tsconfig.json` covers
  all of them — the trusted front end, the pipeline driver and the suites — under
  one fully strict configuration, `noImplicitAny` and `strictNullChecks`
  included. A new file lands in that project by being
  where it belongs; nothing is exempt.
- `tools/source-claims.mts` describes the claims document wire format. A tool
  that writes or reads that document is typed against that description rather
  than against its own idea of the shape, so producer and consumer cannot
  drift apart silently. That typing is the whole consistency mechanism: adding
  or removing a field is a compile error at every site that touches it.
- The trusted front end is TypeScript on the compiler's own API
  (`typescript/unstable/sync` for the checker, `typescript/unstable/ast` for
  the tree), type-checked by the `Front-end types` suite. A member that API
  renamed reads as `undefined` rather than failing, so `tsc` over
  `tools/tsconfig.json` is the thing that catches it — run the suite, do not
  reason about it.
- `pipeline/examples/tsconfig.json` is the strict regime the examples are
  checked under, and a project a case names has its own. The parser refuses a
  file no `tsconfig.json` with `"strict": true` claims, rather than reading it
  under weaker defaults.
- node, not bun: the compiler's synchronous channel reads the child process's
  pipe through node's own `_handle`, which bun does not expose
  (`undefined is not an object (evaluating 'stdout._handle.fd')`). Every tool
  that opens the compiler is affected, so this is not a per-suite choice.
- A unit's boundary is written and what lies inside a unit is inferred:
  every function declaration, class member, function a module binding, a
  class field or `export default` holds, and method of an object literal no
  type gives its context states its parameters' and result's types
  (`isolatedDeclarations` in `tools/tsconfig.json`); locals and functions
  written as arguments are inferred. No value of the sources is typed `any`,
  and they type-check over the external declarations with each `any`
  replaced ([shadow contracts](tools/shadow-contracts.mts)).
  `node tools/unchecked.mts` checks both and reports every boundary and
  assertion; [its header](tools/unchecked.mts) states each rule and its
  stated limit, and `test-all.sh` runs it over `tests/unchecked-project/`
  and `tests/unchecked-broken/`.
- A decoder is the only place that asserts a shape. Everything else narrows:
  a type predicate, a `typeof` before a comparison, a case table keyed by the
  language's own union. `tools/unchecked.mts` reports every `as` and `!` in
  the node side, and fails on one without a reason, a comment
  `// asserted: REASON` at the end of its line or alone on the line above.
  The assertion that has its reason is an `as` at the last
  line of a decoder, where the checks it just ran become the type it returns.
  An assertion anywhere else is standing in for a check that is missing; where
  that check would cost more than it guards, the reason says so.
- Wire formats carry no version, profile or schema tag, and none is to be
  added. What a version would be for is consistency, and consistency here is a
  typing property: each format is one declared type, every producer and
  consumer is typed against that type, and every decoder requires the shape
  field by field and rejects an unknown field. So a document either has exactly
  the current shape or it is refused, and there is nothing for a tag to
  disambiguate. A `sha256` field, where present and checked, can state source
  staleness precisely; the declaration document carries no such hash and
  instead relies on TypeScript's project and source trees.
- A format is never frozen and never has two accepted shapes. Fix its shape in
  place, then regenerate the fixtures that carry it. Do not add a compatibility
  shim, a second decoder, or a field that records which shape a document is:
  every producer and consumer of these documents is in this repository, nothing
  outside reads them, and there is no older document to keep working.
- Lean: no `sorry`, no project axioms.
  [AxiomCheck.lean](lean/Verification/Tests/AxiomCheck.lean) fails the build
  when `checkJson_safe` depends on an axiom other than `propext`,
  `Classical.choice` and `Quot.sound`. No warnings: `lakefile.toml` sets
  `warningAsError`, so a warning fails the build; fix it (a deprecated name's
  replacement, an unused variable as `_`, an unused simp argument dropped)
  rather than silencing it. Build only the module you changed while
  iterating (`lake build Verification.<Layer>.<Module>` from `lean`).
  Run Lake from that directory so elan selects its pinned `lean-toolchain`;
  `lake -d` from the repository root can select a different compiler before
  changing directories. Never run simultaneous builds against the same cache.
  Complete builds before starting suites: the verifier executable must stay
  stable for the whole test run.
- Lean: a definition generic in its labels or store (`ι` and its type-class
  instances) carries `@[nospecialize]`. Lean's code generator otherwise copies
  the whole generic call graph into the first module that uses it at a concrete
  type, which multiplies that module's generated C and its rebuild time.
- Lean: declare a module's inductive types and structures above the proofs
  they do not need. Lean checks a theorem in the background, but adds an
  `inductive`, a `structure` or a `mutual` block only after every earlier
  proof of the module is checked, so one declared below slow proofs holds up
  the rest of the module (HeapExpressionRules: 5.1 s → 3.2 s by moving two,
  measured 2026-10-16).
- New executable fields on an existing AST constructor need an explicit audit
  of every lowering and certification path. Exhaustive constructor matching
  alone cannot detect a discarded field. Each path must check the field's
  execution or refuse it with a located diagnostic. In particular, a lambda
  body certificate does not cover parameter-default execution. Lowering tests
  must exercise source evaluation order and binding scope, including forged
  producer claims against both evidence production and consumption; calculus
  safety alone does not prove correspondence with JavaScript execution.
- Docs: `node tests/docs.mts` checks every link and anchor, section
  numbers in link texts, KaTeX rendering, and the math forms GitHub cannot
  render. A doc-only change runs that check and no suite. Cite papers,
  specifications and issues by a link to an entry of
  [REFERENCES.md](docs/REFERENCES.md), adding the entry there.
- Commits: every commit carries a commit
  record, the format of the [review skill](.claude/skills/review/SKILL.md):
  prose sections, then trailers with `Outcome`, `Parts` and `Trust`. The
  `commit-msg` hook (`make setup-git-hooks`) refuses a message without them.
  A review of agent work is rendered from records
  (`node dev/commit-records.mts`), never written by hand.
- Presentations: record pages and deep-dive decks share one style, and a
  deck is written for a reader with zero context and reaches the owner only
  after a review against the sources ([STYLE.md](docs/STYLE.md)).
- A record uses only the [glossary](docs/GLOSSARY.md)'s terms, plain words
  and the terms of TypeScript and the code, explaining any other term where
  it first appears; before a push, any deep dive the range calls for is
  approved by the owner
  ([the words of a record](.claude/skills/review/SKILL.md#the-words-of-a-record)).
- Status: progress is written once, in the
  [status table](WORK.md#status) of WORK.md. A commit that moves an item
  updates its row. A row states the nature of its work: an investigation whose cause is
  unknown is its own row, named as one, never a leftover of a finished
  stage; a fix gets a row once its cause is established. Elsewhere only three status-like statements are allowed:
  a measurement with its date, an executable expectation
  (`cases.mts` entries) and a spec's proof scope (proved in the model versus
  accepted at the source), changed in the same commit as the code it
  describes. Delete any other prose that restates progress
  ("now", "implemented", "still pending", "restored").
