---
name: parity
description: Continue the work that makes TScert's pass implement the rules of the notes "Tolerant frames" and "Read-only frames", on the line `single-pass` - the goal, the standing decisions, where the plan and its status live, and how the work is run with implementers and a designer. Use when the owner asks to resume or continue the parity work, the plan, or the work on the notes, from a chat with no context.
---

# Making the pass implement the notes' rules

This skill is the whole context a new chat needs. It states the goal, the
decisions that bind every design, where the plan and its status are, and how
the work is run. Read it in full, then the plan's row of
[WORK.md](../../../WORK.md#status), then the design drafts it names.

## The goal

The rules live in two notes,
[Tolerant frames](../../../docs/drafts/tolerant-frames-note/note.tex) and
[Read-only frames](../../../docs/drafts/readonly-frames-note/note.tex),
which builds on the first; together they are the theory and the source of
truth, and "the note" below means either of them. A third note,
[Tolerant frames in practice](../../../docs/drafts/tolerant-frames-patterns-note/note.tex),
applies their rules to pretext's patterns and states none of its own. The
goal is the owner's, in his words:

- "Implementation being in sync with the paper means implementing the same
  rules. Not simply passing the same examples. The examples are just used
  as additional test that the implementation matches the paper."
  (2026-11-14)
- An agent that has only the notes answers "does this example verify?" the
  same way the implementation does, for the part the notes cover; promises,
  for instance, are not covered. (2026-11-15)
- "If it is organised in a very different way then automatically it is not
  aligned." (2026-11-16)

These are one goal. Each definition and each rule of the note is the
definition and the rule that acceptance applies. A decider with its own
soundness proof, which establishes no derivation in the note's rules, does
not meet the goal, however it is proved, and whatever examples agree. The
agreement of a paper-only reader with the verifier is the additional test
of the goal; it does not replace it.

**What counts as in sync.** A rule is in sync when acceptance applies it,
with no separate decider beside it. A proved Lean statement that acceptance
does not run, and a count of agreeing examples, are neither of them
evidence of it. A report on this work says, for each rule it mentions,
what acceptance runs.

**The test.** Each example is given to an agent that has only the two
notes of rules, which answers whether it verifies; the answer is compared with the
verifier's outcome on the example's pipeline case. A disagreement is closed
on either side: the pass changes, or a note changes with the owner's
approval. The test is run as
[the paper-reader test](#the-paper-reader-test).

**Busy work** is work that is required neither for soundness nor on the
critical path to the goal (the owner's definition, 2026-11-15). It is not
queued. Making acceptance apply the note's rules is the goal itself.

**Where two statements of the owner seem to conflict,** both are quoted to
him and he decides. The reading that removes work is not chosen for him.

The note is a model of the verifier, actionable and accurate without being
the implementation; a piece of work starts as a change of the note the
owner approves, and the code is then written to realise it (the owner's
statement, 2026-11-15).

The order of the work:

1. the implementation rules (A), the paper rules (B) and their
   correspondence (C) are made clear, B first, as
   [the basis](../../../docs/drafts/implementation-and-paper-rules.md)
   states;
2. the checking round: every example of the notes of rules is run through
   the verifier and through the paper-only agent, and the three notes are
   read again against the result;
3. then the next pattern of Tolerant frames in practice is taken as a
   change of the note of rules it calls for and realised in the code.

The scope is the general rules and the arithmetic of bound facts that the
text-layout library pretext needs. The note does not give a rule to every
feature of the verifier. A feature outside the scope stays as it is, provided
it cannot make a rule in scope unsound.

## The paper-reader test

`dev/paper-readers.mts` prepares the readers' material and compares their
answers; it launches no reader. The procedure:

1. **Prepare** a directory outside the repository:
   `node dev/paper-readers.mts prepare --out <dir> [--cases <file> |
   --pattern <s> …] [--sample <n> --seed <k>] [--batch <size>]
   [--note <file> …]`. It writes each note of rules (both by default, or
   each `--note`) as `<name>.tex`, `tolerant-frames.tex` and
   `readonly-frames.tex`, the readers'
   instructions as `TASK.md`, each selected case's source as
   `examples/<id>.ts` under a neutral id in a seeded order, with its comments
   removed but for a JSDoc comment carrying an annotation tag, and one
   `batch-<n>.txt` per reader. The key (id → case, declared outcome, area)
   goes to `<dir>.key.json`, beside the directory.
2. **Read.** Each batch goes to an independent subagent on a capable model
   (Claude Opus or Astra), told to work only inside that directory and to
   follow `TASK.md`; it writes `answers-<batch>.json`. A reader never sees
   the key, the case names, the comments or another reader's answers.
3. **Compare:** `node dev/paper-readers.mts compare --dir <dir> [--json]`.
   A positive case is expected to verify, a negative case or a gap to be
   refused; each example is agree, differ or not covered, with totals per
   pattern P1–P21 named in the cases' area texts.
4. **Examine each disagreement before either side changes.** Its cause is
   one of: a note is silent or ambiguous; a note is more general than its
   status tags; the reader erred; the verifier is behind the note.
5. **Judge a revision of the note on a held-out sample** that its reviser
   never saw. On 2026-11-15 a revision reached 108 of 115 on the examples it
   was written from and 23 of 44 on unseen ones; after a revision for
   generality and a stated scope, 25 of 43, with 2 wrong verdicts and 16 not
   covered. Agreement on the examples a revision was written from does not
   measure the note.

Every report gives three counts, agree, not covered and differ, for the
catalogue cases, for the notes' own examples and for a held-out sample.
Each note changes only with the owner's approval.

## Where things are

- The line is the branch `single-pass`. `main` is behind it, and `main`'s
  CLAUDE.md is stale where it differs from this line's.
- The owner's checkout, `~/GitHub/TScert`, stays on `single-pass`, so that
  a new chat opened there reads this line's instructions. After each merge
  into the line it is fast-forwarded
  (`git -C ~/GitHub/TScert merge --ff-only origin/single-pass` after a
  fetch). Nothing is built, edited or created in it.
- The owner follows the work in WORK.md of that checkout. A report of the
  plan's state reads WORK.md on `origin/single-pass` and names its commit;
  a copy of a file handed to the owner names the commit it shows.
- The plan and its status: the row "Pretext's walkers under the read-only
  frame" of [WORK.md](../../../WORK.md#status), its steps numbered (1.1 to
  1.7, 2.1 to 2.5, 3), each with its state and, while in progress, the
  branch holding it; the row "Implementation rules and paper rules" states
  how the implementation corresponds to the notes. Status is written there
  and nowhere else; a commit that moves an item updates the row.
- The comparison of the notes with the implementation, rule by rule:
  [parity-rule-table.md](../../../docs/drafts/parity-rule-table.md).
- The designs: [parity-interfaces.md](../../../docs/drafts/parity-interfaces.md)
  (shared definitions) and
  [effects-of-commands.md](../../../docs/drafts/effects-of-commands.md)
  (effects stated per exit, the effect of a command, four migration steps),
  [rules-at-acceptance.md](../../../docs/drafts/rules-at-acceptance.md)
  (composition used by acceptance, checked transfer, rule Loop with its
  frame, the checking round).
- Each note's page and PDF are built in its directory
  (`tolerant-frames-note`, `readonly-frames-note`,
  `tolerant-frames-patterns-note`): `python3 build.py` (page, through
  pandoc), `python3 color.py && latexmk -pdf note-color.tex` (PDF, copied
  to the tracked PDF of that directory). Build products other than the
  tracked PDF are removed after a build.

## Decisions that bind every design

Each was made by the owner. A design that needs to depart from one stops and
asks.

- **Each note changes only with the owner's approval.** Show the difference,
  wait for his word, then commit. A status tag (`Lean:`, `conj.`,
  `assumed`) is the exception: it follows the state of the proofs on the
  line and is updated without asking. Where Lean proves less than the note, Lean
  changes. The note is precise, defines each key concept once as a numbered
  definition, gives an example for what it introduces, and does not grow
  beyond what pretext needs.
- **The reduction is deterministic and the safety definition is unchanged.**
  Behaviour that depends on the host is a host value assumed to meet a
  specification; the soundness theorem quantifies over such values. This is
  how `await`, `push` and the typed array's read, write and length are
  modelled. No nondeterministic reduction rule is introduced.
- **A typed array is a primitive in its storage** (a descriptor with format
  and fixed length, and a tagged view spine without holes) **and its three
  steps are specified axiomatically** by the note's rules View-Length,
  View-Read and View-Write. The model has no buffer.
- **Regions are interpreted from the heap alone.** A location's class (value
  location, array spine, view spine) is decided by its contents; one theorem
  connects this to the kinds the world records. Kinds are used in worlds,
  contracts, reference validity and separation evidence.
- **Arithmetic in scope:** linear arithmetic over safe integers; what passing
  pretext code already uses beyond it (shift right by a constant, mask by a
  constant, string length with reads and concatenation). Products of two
  variables, shift left and bitwise or stay outside, as entries of Tolerant
  frames in practice.
- **Closure specifications over captured variables:** separate work, later.
- **The exact update of a typed array stays inside its rule.** The contract
  language does not grow for it.
- **A specification with a rest parameter is a schema.** Its rest variable
  denotes the sequence of supplied argument values, and rule Call
  instantiates it at the evaluated argument list, spread expansion
  included. A function body is checked for every such sequence, which
  equals the initial contents of its fresh rest array.
- **A specification is closed.** Its postconditions mention its own
  parameters, receiver, result and heap, and no formula of the assertions
  a particular unit's check collected.
- **An assertion is read at a state, with its world.** The modality
  quantifies over the states admissible from that state. Two
  specifications of one function conjoin (rule Conj of the note) when the
  second's postconditions are independent of the world.
- **Trust.** That host and library values meet their declared contracts is
  the standing trust in the library model. A consequence of it is stated
  where that trust is stated and is not presented as a new assumption. A
  change of a specific contract is named in the commit's `Trust` trailer.
- **There is no OCaml producer.** It is removed for good. The serialized
  documents are written by `tools/*.mts` and read by Lean. Instructions that
  mention it are stale.
- **The serialized format between front end and verifier has one shape.** A
  change of shape lands in one commit with every writer, the reader and the
  stored examples.

## How the work is run

### Roles

- **The orchestrator** is the main chat. It directs, reads results, decides
  by the principles here, talks to the owner, opens and merges pull
  requests. It does small edits itself (a paper paragraph, a rebase, a
  conflict in a list of imports) and delegates the rest.
- **Implementers** are subagents on Claude Opus (the Agent tool, general
  purpose, `model: "opus"`), never a smaller model. One implementer owns one
  set of files at a time. Two run in parallel only on disjoint files. Each
  gets the [brief](brief.md), filled in.
- **The designer and reviewer** is Astra, read-only:

  ```sh
  codex exec -m gpt-6-astra -s read-only --ephemeral -o <out.md> "$(cat <prompt.md)" < /dev/null > <trace.log> 2>&1
  ```

  run in the worktree it should read, in the background. Every prompt states
  the goal and direction, the owner's decisions that bind it, and the exact
  question. Before a run, read the weekly usage (a one-word non-ephemeral run,
  then the last `used_percent` in the newest file under `~/.codex/sessions`),
  and tell the owner when a run fails on the limit, so he can reset it.

### When Astra is used

- **Before implementation:** every design and every plan, as
  [designs](../../../CLAUDE.md#designs-start-from-an-existing-mechanism)
  states.
- **After implementation, once per piece of work:** when the piece changes a
  decision of the pass, the acceptance path, a rule's statement, or what is
  assumed of the host. The review is asked rule by rule against the note.
- **Not needed:** a piece that only adds definitions and theorems nothing in
  the pass reads yet, with the suite green; a rebase; a docs-only change
  other than the note's rules.
- **Its answers are checked.** A justification Astra gives is compared with
  how the system already handles the case it cites before it is relayed or
  acted on. Its finding "fix first" goes back to the implementer of the
  piece; a finding the implementer disputes is reported with both sides.

### Tests

- **Implementers do not run the full suite**, the pretext tier or cost
  measurements. Their gates are the Lean build with the axiom check, the
  static checks (`node tests/docs.mts`, `(cd tools && npx tsc -p
  tsconfig.json)`, `node tools/unchecked.mts`, `node
  tests/json-field-names.mts`) and the cases their change touches (`node
  pipeline/run-cases.mts <pattern>`).
- **Every command has a limit near its healthy duration**, about twice it:
  a build at most 10 minutes, a pattern of cases at most 5. Nobody waits an
  hour on a 5-minute check. A wait loop must end by itself; a loop on
  `pgrep -f` that matches its own command line never does.
- **The full suite runs once, in CI, on the pull request.** A local full run
  is done only by the orchestrator, supervised, one at a time, watching its
  log advance.
- A piece of work whose point is cost is measured by the orchestrator, at a
  load average below about 12, base and tip interleaved.
- Leftover processes of finished implementers are stopped when found, after
  checking nothing real runs behind them, and the owner is told.

### Worktrees, commits and pull requests

- Nothing is created under `~/GitHub/` without the owner's instruction.
  Worktrees and scratch live in a temporary directory outside it; a new
  worktree is made from `origin/single-pass` and its `lean/.lake` and
  `node_modules` are copied from a built worktree with `cp -c -R` (see
  CLAUDE.md, "Working in a separate git worktree").
- Every commit carries a commit record ([review skill](../review/SKILL.md));
  `bin/git_hooks/commit_record.sh <message> --check` checks one.
- Work reaches the line as pull requests against `single-pass`, stacked
  where one depends on another. A pull request is merged by fast-forward
  when its two checks, `render` and `test`, have passed:
  `git push origin <tip>:refs/heads/single-pass` after confirming the line's
  tip is an ancestor. A docs-only pull request rebased onto a moved line is
  merged after its docs check passes locally. The owner has given this
  standing instruction for the line; a push to `main` needs his word each
  time.
- A change to a note is pushed only after the owner approved its text.

### Talking to the owner

- Short and precise. The result first; a few sentences.
- Standard terms of type theory and programming-language semantics, and the
  note's own terms (postcondition, effect, region, change, class region).
  No coined words, no internal labels, no Lean identifiers unless he asks.
- A claim is as strong as its evidence: say what was run and what was only
  read. Say the implementation is in line with the notes only from the
  comparison with a paper-only reader, giving its counts and its
  disagreements.
- An ambiguous request is answered with its most plausible reading and the
  next step. Obvious next steps are taken, not asked.
- A design question that the principles here do not settle is put to him as
  a choice of routes with a recommendation.
- When he asks to see a change to a note, he gets the difference, and the
  page for comments; rendered pages are checked for unconverted LaTeX.

## Starting from nothing

1. `git fetch origin`; make a worktree of `origin/single-pass` outside
   `~/GitHub/`; build it (`cd lean && lake build`, `make setup`).
2. Read this file, the plan's row in WORK.md, the design drafts it names,
   and the open pull requests against `single-pass` (`gh pr list --base
   single-pass`).
3. Continue the first step of the plan that is not done. A step in
   progress names its branch in the row; it is on GitHub, so make the
   worktree from `origin/<branch>` and read its last commit records, which
   say what the next run starts from. A step with no design gets one first,
   then implementers by the brief, review, pull request.
