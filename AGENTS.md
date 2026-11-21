# Working in TScert

An independent verifier for type claims about TypeScript programs: a calculus
with a semantic model and soundness proofs in Lean, a single pass that
computes and checks each unit's types and facts, and a pipeline that parses a
TypeScript source and asks the pass whether each unit is safe.
[README.md](README.md) is the entry point; [DESIGN.md](docs/DESIGN.md) holds the
decisions. This guide holds the rules every agent follows here, the
commands, and links to the documents that own each procedure.

## Continuing the work on the notes

The work that makes the pass implement the rules of the notes "Tolerant
frames" and "Read-only frames" is described, with its decisions, its roles
and how to resume it from nothing, in
[the parity skill](.claude/skills/parity/SKILL.md); its state is one row of
[WORK.md](WORK.md#status).

## Commands

```sh
make help        # every target
make test        # make test-checks, then make test-cases
make test-checks # build, then the fast checks and the controls, replayed from the store
make test-infra  # build, then the tests of the test infrastructure (store, runner, replay, observed stages, sessions)
make test-cases  # build, then the pipeline cases
make cases P=x   # the pipeline cases whose file names contain x
make check FILE=f.ts [PROJECT=dir] [CONTRACTS=1]  # one source file through the pipeline; CONTRACTS=1 adds the external contracts it relies on
make lowering FILE=f.ts [FN=name]   # the execution graphs a source's functions lower to
make semantic-diff REV=rev          # render the commit records of a commit or range
make build       # build-lean and build-runner: the Lean verifier and the stage runner
make setup       # the node dependencies
make clean-store # remove stage entries, timeout observations and the source snapshots no running process holds
make test-pretext PRETEXT=checkout [FILES=…]  # the pretext tier
make census [DIR=tools] [FILES=…] [FUNCTIONS=…] [SHALLOW=1] [SHARD=i/n]  # the census of a directory's functions
make fmt         # Prettier over the .json and .ts files .prettierignore admits; make check-fmt checks
```

[tests/README.md](tests/README.md) indexes the cases, the controls and the
suites.

### The stage store

Every stage and every control's operation replays from
[the stage store](docs/STAGE-STORE.md) by content, through
[one mechanism](pipeline/stages.mts). The front end reads the file system
only through `tools/files.mts` and opens its compiler only through
`openFrontEndCompiler` (`tools/compiler-channel.mts`). A new file of
`pipeline/` or `tools/` that only orchestrates or presents goes on
`unkeyed` (`pipeline/stage-execution.mts`), its role stated in
[keys](docs/STAGE-STORE.md#keys), in the same commit. A branch uses the
default store, shared by every checkout and worktree; an agent testing the
store itself names one under `$TMPDIR` (`TSCERT_STAGE_STORE`). A process
stage is killed after 60 s, a control's operation after 30 s, and a stage
at 8 GiB of memory, a tool failure never published
([entries and timeouts](docs/STAGE-STORE.md#entries-and-timeouts)).

### Iterating: run what the change touches

Checks fall in rough cost classes: **seconds** (one case, one Lean module,
`node tests/docs.mts`, `tsc`), **minutes** (the cases of a pattern, the
controls, an incremental `lake build`), **tens of minutes** (all cases,
`make test`, the pretext tier, a clean `lake build` in a new worktree,
which is why a worktree clones `.lake`) and **hours** (the census).

Run the cheapest check the change can make fail. Widen only when the
change can reach what the wider check covers and the narrower ones pass.
Run each wide check once per change (the full suite in the pull request's
`test` job, the census once after a merge), never again on an unchanged
tree. A doc-only change runs `node tests/docs.mts` alone. A case that
fails on a timeout while the machine is loaded is rerun by its pattern.
The table is the principle's instance:

| Changed | While iterating | Before merging |
| --- | --- | --- |
| One source file | `node pipeline/verify-source.mts <file.ts>` | — |
| Lean | `(cd lean && lake build)`, then `node pipeline/run-cases.mts <pattern>` for the affected cases | `make test` (the cases, and the controls: forged fragments and forced proposals no case can make) |
| Parser, Fragment wire, shared tools | `(cd tools && npx tsc -p tsconfig.json)`, `node tests/json-field-names.mts`, then `run-cases.mts` | `make test` |
| Cases, examples | `run-cases.mts <pattern>` for the cases touched | — |
| Bounds capability for pretext | `make test-pretext PRETEXT=<checkout> FILES=<touched>` | `make test-pretext PRETEXT=<checkout>`; CI's `pretext` job runs it at its pinned pretext commit |

### Measuring coverage: once, on main

<!-- OWNER: work lands on `single-pass`; do the census and the gap rounds run on `main` or on `single-pass`? -->

Work lands on the line `single-pass`
([where things are](.claude/skills/parity/SKILL.md#where-things-are)). The
census runs on `main` once after each merge, by the
[Census workflow](.github/workflows/census.yml); its commands are
[`dev/census.mts`'s](dev/census.mts). A branch runs no census, over
`tools/` or over a file: it shows a change does what it is for by the
function it targets and one depending on it, before and after
(`make census FILES=f.mts FUNCTIONS=fn,other SHALLOW=1`). A coverage report
states the count, denominator and scope, and labels statement coverage and
aggregates separately
([function coverage](docs/DESIGN.md#function-coverage-and-release-thresholds)).

### Choosing the gap cases to work on

Gap work follows the [gap-round skill](.claude/skills/gap-round/SKILL.md),
which states its policy, from the census of main. A refusal of TScert's own
code takes the first of the seven routes of
[deciding what a refusal calls for](docs/SOURCE-REWRITES.md#deciding-what-a-refusal-of-tscerts-code-calls-for)
that establishes the obligation at acceptable cost; a repair, an avoidance
or a host boundary is recorded there in the same commit, with what its kind
requires. A case is a negative case only where its program is unsafe, shown
under Node.

### How a pull request lands

A branch is ready to merge when `make test` passes in CI, the `test` job of
its pull request. An implementing subagent runs the build, the static
checks and the cases its change touches, each under a limit near its
healthy duration, and never the full suite
([the parity skill](.claude/skills/parity/SKILL.md#tests)).

<!-- OWNER: which models author, merge and review (Claude Opus 5.5, Astra, Fable), here and in "Designs start from an existing mechanism"? -->

The trusted model (Claude Opus 5.5 or Astra) that authors the change, or
merges it when its author is another model, merges it when confident the
change is correct and sound, a new rule's or a change of trust's soundness
included, and asks for a review only when it is not.

<!-- OWNER: which checks gate a merge on GitHub: `render` alone, or `render` and `test`? -->

`single-pass` and `main` keep linear history: a pull request lands by
rebase and merge, or by a fast-forward of the line to its tip
([the parity skill](.claude/skills/parity/SKILL.md#worktrees-commits-and-pull-requests)).
Each pull request runs `render`
([semantic-diff.yml](.github/workflows/semantic-diff.yml)) and the `test`
and `pretext` jobs ([ci.yml](.github/workflows/ci.yml)). A merged pull
request is not evidence that its suites passed: whoever reports a change
as tested names the `test` run or the local `make test` it read, and a
`test` failure on the line is fixed on the line at once.

### Working in a separate git worktree

A new worktree clones the main checkout's Lean cache before its first
build (copy on write; Lake rebuilds by content), and removes the copied
executable, whose `verifier.rsp` names the main checkout's objects, so Lake
relinks it from the worktree's own:

```sh
cp -c -R <main checkout>/lean/.lake lean/.lake
rm lean/.lake/build/bin/verifier
(cd lean && lake build verifier)
```

Each worktree keeps its own `.lake`, so builds in different worktrees may
run in parallel. Each installed `node_modules` (the root's, `tools/`'s and
`pipeline/library-project/`'s) is copied the same way, never linked or
committed: a link resolves type declarations from the main checkout's path
and the cases reading `@types/node` fail. `make setup` and the case runner
make the fixture projects' links.

## Which tests to keep

A new feature's test is a pipeline case, a source with its expected
outcome, positive and negative. Any other test exists only for what the
pipeline cannot show (a refusal no source can reach, a trusted input's
boundary, a speed-critical check): a control of
`tests/single-pass-controls.mts` for an input no case makes, a suite of
`test-all.sh` for a check running no stage. A research test is retired once
a case covers its behaviour, and a test that adds no signal is removed. The
rules: [which tests to keep](tests/README.md#which-tests-to-keep) and
[the suite's shape](tests/README.md#the-suites-shape).

## Acceptance/soundness invariant

A unit's accepted verdict from the verifier's CLI implies the modeled
safety property for every function of that unit, by construction: one
headline theorem, `SourceClaimJson.PassUnit.mode8Accepted_sound`, whose
premise is the exact CLI condition for an accepted verdict at either print
site, and one exhaustive conversion of every plan to `CertifiedPlan`, which
a new plan constructor fails to compile until its checker and theorem
exist. The rules that keep it, and the premise and conclusion to review
when the plan type or CLI path changes:
[what "verified" means](docs/DESIGN.md#what-verified-means).

## Source and host soundness boundaries

### General statements, no lists of special cases

A definition, a rule or a theorem is stated at the generality of its notion,
as a type-theory paper states it: over every expression, command, write,
step, transition, effect and function. For a notion the
[Tolerant frames note](docs/REFERENCES.md#the-tolerant-frames-note) or the
[Read-only frames note](docs/REFERENCES.md#the-read-only-frames-note)
defines, the Lean and the note state the same definition, in full. Where
the model shows the note wrong or incomplete (a counter-model, a notion the
model has and the note omits), the note is corrected and the Lean follows
it; the Lean is never bent to a wrong sentence, and a difference between
the two is never left standing.

- **A list of supported cases is a defect.** An enumeration of members of an
  open class (native operations, kinds of write, kinds of fact, eligible
  functions, forms that have an entry) that stands for a property is
  replaced by the property. A restricted encoding of a general notion, a
  fallback that gives less without saying so, and a side condition of the
  form "X is not read by Y" are the same defect.
- **An exhaustive case analysis is a proof:** cases over an inductive
  definition of the language, which Lean checks exhaustive, prove a general
  statement.
- **A special case states its reason:** which property a specific rule
  relies on, and where it is defined.
- **A restriction of the language is explicit:** chosen by the behaviour it
  excludes, documented in SOURCE-FRAGMENT.md and enforced at the source
  boundary ([engineering trade-offs](#engineering-trade-offs)).
- **Touching a special case removes it first:** a change to code holding
  such a list starts by replacing the list with its general statement, in
  its own commit. A report or a review that says "covers only", "for these
  forms", "eligible" or "supported cases" names which of the three above it
  is.

Every review of a design, a rule or a proof asks first: is this the notion
as its definition states it, and is the statement general. Size and the
smallest change come after.

### Designs start from an existing mechanism

A new mechanism, or a change to a rule acceptance applies, is designed in
a draft (`docs/drafts/`) before it is built. A small change (a diagnostic,
a fix or an extension inside an existing mechanism) has no design step: it
is implemented, then reviewed by Astra or Fable, the review asking the
first question below. A design draft opens with a section **The existing
mechanism this extends**, citing the document that owns it (for a fact a
construct relies on across code, [footprints](docs/FOOTPRINTS.md): the
fact, its stable operations, the checked contract, the construct's rule).
[The general mechanisms](docs/DESIGN.md#general-mechanisms) lists each
concern's mechanism. Where no mechanism fits, that section lists the
mechanisms considered and why each falls short; no new machinery is
proposed before it is written. Every review of a design or of a new rule
asks first: is this an instance of an existing mechanism, and which; what
does it duplicate? For an external API, follow
[modeling a library](docs/SOURCE-CONTRACTS.md#modeling-a-library).

That section states the existing mechanism as pseudo-code read from the
code (its definitions named), one small example run through it, the
proposed change, and the example run through the change, step by step.
It ends with **What this duplicates**: each thing the design models
(natives, outside values, module bindings, the initialization, effects,
kinds of step) beside where the rest of the verifier models the same
thing, and why the design reads that model or what keeps it apart. A
model shaped to one example (a list of one native, a value chosen by a
name) is a special case of the kind
[General statements](#general-statements-no-lists-of-special-cases)
excludes, and a later step that meets its limit reopens it rather than
patching around it. A brief to a reviewer or an implementer states the
same question first, and a reviewer's verdict answers it before
soundness. An estimate of a design's size is measured from the code it
changes (the definitions and the files that read them); one not measured
says so.

The same holds wherever a mechanism, a decision or a finding is
communicated (a report, a question to the owner, a brief, a review): it
is shown on a concrete program, run through the mechanism as it is and
as it would be, with what each step decides and why, before or beside
any abstract statement. A decision put to the owner states what each
choice does to that program.

### Engineering trade-offs

An explicit, enforced restriction, chosen by the behaviour it excludes and
not by a failing example, is an acceptable decision
([utility justifies complexity](docs/DESIGN.md#principles)): documented in
SOURCE-FRAGMENT.md, enforced at the source/semantic boundary, required of
external code where relevant, with a small control showing the excluded
behaviour cannot silently enter. It simplifies the language, never the
meaning of an accepted program. A motivating ordinary program that stays
blocked is open work in WORK.md.

Annotations and native contracts are review obligations no proof
discharges ([review obligations](docs/SOURCE-CONTRACTS.md#review-obligations)):

- **Never erase an unsupported contract:** annotation lowering represents
  the whole contract or refuses it; an opaque type is not `unknown`.
- **Native declarations are specifications to audit, not evidence**
  ([modeling a library](docs/SOURCE-CONTRACTS.md#modeling-a-library));
  collect exactly the intrinsics a source uses.
- **Array construction is ordinary, also of external code**; never widen
  that assumption silently.
- **Array presence is separate from read/write capability.**
- **Inferred callable effects** follow the
  [elaboration/certification boundary](docs/SOURCE-ELABORATION.md#inferred-call-effects-elaboration-and-certification):
  annotation translation never strengthens an ordinary arrow; the
  definition's check establishes safety and the effect before an
  application consumes it. An effect without `onThrow` guarantees
  preservation only on normal return, never on a call's exceptional edge
  or to a caller catching without checking its handler against the changed
  heap ([exceptional footprints](docs/SOURCE-ELABORATION.md#exceptional-footprints)).
- **Test the unproved boundary independently:** a forged-fragment control
  for annotation interpretation, a Node run of a native-contract repair's
  negative fixture.
- **Coverage losses are results**, reported, never reclassified away.
- **Never gain acceptance by increasing trust silently.**

## Conventions

- Node side: every module is `.mts`, in the one fully strict project
  `tools/tsconfig.json` by its location, nothing exempt; run node, not bun
  (the compiler's synchronous channel reads node's `_handle`). A member the
  compiler API renamed reads as `undefined`, so `tsc` over that project
  catches it: run it, do not reason about it.
- A unit's boundary is written and what lies inside it is inferred, no
  value is typed `any`, and every `as` and `!` carries a reason
  (`// asserted: REASON`), as [`tools/unchecked.mts`](tools/unchecked.mts)
  states and checks. A decoder is the only place that asserts a shape;
  everything else narrows.
- `tools/fragment.mts` and `tools/declaration-types.mts` describe the
  parser's document, Lean's decoder refuses any other shape, and
  `tests/json-field-names.mts` compares both sides' field names. Wire
  formats carry no version, profile or schema tag and have one shape,
  changed in place with their fixtures
  ([lasting decisions](docs/DESIGN.md#lasting-decisions)).
- The parser refuses a file no `tsconfig.json` with `"strict": true`
  claims; `pipeline/examples/tsconfig.json` is the examples' regime.
- Lean: no `sorry`, no project axioms (the
  [axiom check](lean/Verification/Tests/AxiomCheck.lean),
  [the paper's](lean/Verification/Paper/TolerantFrames/Tests/AxiomCheck.lean),
  `tests/axiom-check-imports.mts`), and no warnings (`warningAsError`): fix
  a warning, never silence it. Build the changed module while iterating,
  from `lean/` so elan selects its toolchain; never run two builds on one
  cache; finish building before starting suites, so the verifier stays
  stable for the whole run. A definition generic in
  its labels or store (`ι` and its instances) carries `@[nospecialize]`;
  a module declares its inductive types and structures above the proofs
  that do not need them.
- A new executable field on an existing AST constructor is audited on every
  lowering and certification path, each checking its execution or refusing
  it with a located diagnostic (a lambda body certificate does not cover
  parameter defaults); lowering tests exercise evaluation order and binding
  scope, forged fragments and forced proposals included, since calculus
  safety alone does not prove correspondence with JavaScript execution.
- A change to an annotation TScert reads updates
  [ANNOTATIONS.md](docs/ANNOTATIONS.md) in the same commit. Cite papers,
  specifications and issues by an entry of
  [REFERENCES.md](docs/REFERENCES.md).
- Every commit carries a commit record in the format of the
  [review skill](.claude/skills/review/SKILL.md), which the `commit-msg`
  hook (`make setup-git-hooks`) checks; a review of agent work is rendered
  from records (`node dev/commit-records.mts`), never written by hand. A
  record uses only the [glossary](docs/GLOSSARY.md)'s terms, plain words
  and the terms of TypeScript and the code, explaining any other where it
  first appears; before a push, any deep dive the range calls for is
  approved by the owner
  ([the words of a record](.claude/skills/review/SKILL.md#the-words-of-a-record)).
- A deck is written for a reader with zero context and reaches the owner
  only after a review against the sources; the owner's approval moves its
  `SINCE=` ([STYLE.md](docs/STYLE.md)).
- Progress is written once, in the [status table](WORK.md#status) of
  WORK.md, which states how a row moves. An investigation whose cause is
  unknown is its own row, never a leftover of a finished stage; a fix gets
  a row once its cause is established. Elsewhere only a dated measurement,
  an executable expectation (`cases.mts` entries) and a spec's proof scope
  (proved in the model versus accepted at the source) state status, each
  changed with the code it describes; other prose restating progress
  ("now", "implemented", "still pending", "restored") is deleted.
