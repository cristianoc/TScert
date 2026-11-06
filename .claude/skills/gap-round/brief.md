# Brief: make one gap case of TScert's own code verify

The orchestrator fills `<case>`, `<reason>`, `<sites>`, `<census record>`
and `<scratch>` (the orchestrator's scratchpad) before sending.

You work in your own git worktree of TScert, starting from main. Rebase
onto main's tip before your first commit if main has moved. Read CLAUDE.md
first. It is the authority, and this brief only fills in the round.

## The case

- Case `<case>`: `pipeline/examples/<case>.ts`, a gap in `pipeline/cases.mts`.
- Its reason: `<reason>`.
- The census sites it stands for: `<sites>`. They come from `<census record>`,
  each a unit's refusal at its span in `tools/<file>`.

The goal is that the case is closed: decided, never left a gap. Answer it
by the first route of
[deciding what a refusal calls for](../../../docs/SOURCE-REWRITES.md#deciding-what-a-refusal-of-tscerts-code-calls-for)
that establishes the obligation at acceptable cost, deciding whether the
construct is worth supporting or the code is rewritten instead. Repair the
sites where TScert's own code discards what it knew. Record a repair, an
avoidance or a host boundary in SOURCE-REWRITES.md in the same commit.

- **Supported:** the case verifies.
- **Rewritten instead:** TScert's code takes an equivalent form that
  verifies; the case is written in that form and verifies, and the avoided
  form is recorded with its reason under "Constructs avoided" in
  SOURCE-REWRITES.md.
- **Unsafe:** only a program that is unsafe, shown by running it under
  Node, becomes a negative case.

- **A library or host function TScert does not model yet:** write its
  model, stating the trust it takes, and proceed. The owner reviews it
  before the push.
- **Trust you can add yourself:** only the approved assumption that
  standard objects are not tampered with. Anything else is stated in the
  model and in your report.
- **When no principle decides a question:** stop and report the missing
  principle in one or two sentences.
- **If the case does not reproduce the census refusal:** find the real
  cause from the census sites, and make the case that reproduces it.
- **A case with no census sites:** TScert's code no longer meets the
  construct, having been rewritten. Decide whether the construct is worth
  supporting: support it, or keep the rewrite, write the case in the
  rewritten form so it verifies, and record the avoided form.

## Soundness

- Follow CLAUDE.md's "What a result means" and "Source and host soundness
  boundaries" exactly.
- A new rule needs:
  - its Lean checker and theorem, with no `sorry`, no axioms and no
    warnings;
  - a positive and a negative pipeline case;
  - controls with forged claims, where claims are involved.
- A repair of a native contract also runs its negative fixture under Node.
- Prefer the one general mechanism to a patch for one construct.
- A new rule or design names first the existing mechanism it extends
  ([designs start from an existing mechanism](../../../CLAUDE.md#designs-start-from-an-existing-mechanism)).

## Working rules

- **Files:** create nothing under `~/GitHub` outside your worktree. Scratch
  goes under `<scratch>/<case>/` and is deleted when you are done, except
  your report.
- **Setup:** follow CLAUDE.md's "Working in a separate git worktree" for
  `lean/.lake`. Copy the `node_modules` directories from the main checkout
  with `cp -c -R`: `tools/`, the root's, and each `pipeline/*/` one. Then
  run `make build-runner`. Never commit these.
- **Heavy runs** are serialized across agents. Wrap every `make test`,
  `make test-checks` and `make test-cases`, every `make census …` and every
  `run-cases.mts` with no pattern:

  ```sh
  until mkdir <scratch>/heavy.lock 2>/dev/null; do sleep 20; done; <command>; rmdir <scratch>/heavy.lock
  ```

  Release the lock on failure too.
- **Measuring:** take the function the case blocks most and one that
  depends on it, before and after, under the lock. Run
  `make census FILES=f.mts FUNCTIONS=fn,other SHALLOW=1`, with the default
  stage store ([the stage store](../../../AGENTS.md#the-stage-store)). Run
  no full census.
- **Committing:**
  - `make test` passes before each commit.
  - Each commit carries a record in the format of
    `.claude/skills/review/SKILL.md`, in the words its section "The words
    of a record" states.
  - Commit small green steps, and update WORK.md's row when the work moves
    an item.
  - Never push, and never merge into main.

## Report (concise)

- The branch and worktree path.
- The commits: hashes and subjects.
- The route you took, and why.
- The Effect lines: each case before → after.
- The measured functions before → after.
- Any model of external code, with the trust it states.
- Anything still open.
