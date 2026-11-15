---
name: parity
description: Continue the work that makes TScert's pass implement the rules of the note "Tolerant frames", on the line `single-pass` - the goal, the standing decisions, where the plan and its status live, and how the work is run with implementers and a designer. Use when the owner asks to resume or continue the parity work, the plan, or the work on the note, from a chat with no context.
---

# Making the pass implement the note's rules

This skill is the whole context a new chat needs. It states the goal, the
decisions that bind every design, where the plan and its status are, and how
the work is run. Read it in full, then the plan's row of
[WORK.md](../../../WORK.md#status), then the design drafts it names.

## The goal

The note [Tolerant frames](../../../docs/drafts/tolerant-frames-note/note.tex)
is the theory and the source of truth. The pass is in line with the note when
it implements the note's rules: each definition, law, axiom and rule of the
note has the same statement in Lean and is the mechanism the pass applies.
Examples that pass are a test of that match and no substitute for it. A
mechanism of the pass with no rule in the note is out of line too: it gets a
rule in the note or it is deleted.

The order of the work:

1. the implementation is brought to the note's rules;
2. then every example the note supports is run through the verifier, and the
   two notes are read again against the result;
3. then the second note,
   [Tolerant frames II](../../../docs/drafts/tolerant-frames-2-note/note.tex),
   is rewritten as the examples the first note does not handle.

The scope is the general rules and the arithmetic of bound facts that the
text-layout library pretext needs. The note does not give a rule to every
feature of the verifier. A feature outside the scope stays as it is, provided
it cannot make a rule in scope unsound.

## Where things are

- The line is the branch `single-pass`. `main` is behind it, and `main`'s
  CLAUDE.md is stale where it differs from this line's.
- The owner's checkout, `~/GitHub/TScert`, stays on `single-pass`, so that
  a new chat opened there reads this line's instructions. After each merge
  into the line it is fast-forwarded
  (`git -C ~/GitHub/TScert merge --ff-only origin/single-pass` after a
  fetch). Nothing is built, edited or created in it.
- The plan and its status: the row "The pass implements the note's rules" of
  [WORK.md](../../../WORK.md#status). Status is written there and nowhere
  else; a commit that moves an item updates the row.
- The comparison of the note with the implementation, rule by rule:
  [parity-rule-table.md](../../../docs/drafts/parity-rule-table.md).
- The designs: [parity-interfaces.md](../../../docs/drafts/parity-interfaces.md)
  (shared definitions) and
  [effects-of-commands.md](../../../docs/drafts/effects-of-commands.md)
  (effects stated per exit, the effect of a command, four migration steps).
- The note's page and PDF are built in its directory: `python3 build.py`
  (page, through pandoc), `python3 color.py && latexmk -pdf note-color.tex`
  (PDF). Build products other than the tracked PDF are removed after a build.

## Decisions that bind every design

Each was made by the owner. A design that needs to depart from one stops and
asks.

- **The note changes only with the owner's approval.** Show the difference,
  wait for his word, then commit. Where Lean proves less than the note, Lean
  changes. The note is precise, defines each key concept once as a numbered
  definition, gives an example for what it introduces, and does not grow
  beyond what pretext needs.
- **The reduction is deterministic and the safety definition is unchanged.**
  Behaviour that depends on the host is a host value assumed to meet a
  specification; the soundness theorem quantifies over such values. This is
  how `await`, `push` and the typed array's read, write and length are
  modelled. No nondeterministic reduction rule is introduced.
- **A typed array is a primitive in its storage** (a descriptor with format
  and fixed length, and a tagged view store without holes) **and its three
  steps are specified axiomatically** by the note's rules View-Length,
  View-Read and View-Write. The model has no buffer.
- **Regions are interpreted from the heap alone.** A location's class (value
  location, array store, view store) is decided by its contents; one theorem
  connects this to the kinds the world records. Kinds are used in worlds,
  contracts, reference validity and separation evidence.
- **Arithmetic in scope:** linear arithmetic over safe integers; what passing
  pretext code already uses beyond it (shift right by a constant, mask by a
  constant, string length with reads and concatenation). Products of two
  variables, shift left and bitwise or stay outside, as entries of the second
  note.
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
  then the last `used_percent` in the newest file under `~/.codex/sessions`);
  stop using Astra at 95%.

### When Astra is used

- **Before implementation:** every design and every plan that is not a small
  local change. The design opens with "The existing mechanism this extends".
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
- A change to the note is pushed only after the owner approved its text.

### Talking to the owner

- Short and precise. The result first; a few sentences.
- Standard terms of type theory and programming-language semantics, and the
  note's own terms (postcondition, effect, region, change, class region).
  No coined words, no internal labels, no Lean identifiers unless he asks.
- A claim is as strong as its evidence: say what was run and what was only
  read. Never say the implementation is in line with the note from example
  outcomes.
- An ambiguous request is answered with its most plausible reading and the
  next step. Obvious next steps are taken, not asked.
- A design question that the principles here do not settle is put to him as
  a choice of routes with a recommendation.
- When he asks to see a change to the note, he gets the difference, and the
  page for comments; rendered pages are checked for unconverted LaTeX.

## Starting from nothing

1. `git fetch origin`; make a worktree of `origin/single-pass` outside
   `~/GitHub/`; build it (`cd lean && lake build`, `make setup`).
2. Read this file, the plan's row in WORK.md, the two design drafts, and
   the open pull requests against `single-pass` (`gh pr list --base
   single-pass`).
3. Continue the first item of the plan that is not done: design by Astra if
   it has none, then implementers by the brief, review, pull request.
