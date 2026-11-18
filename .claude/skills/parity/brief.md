# Brief: one piece of the parity work

The orchestrator fills `<worktree>`, `<branch>`, `<base>`, `<scratch>`,
`<design section>`, `<files>`, `<work>` and `<gates>` before sending. The
implementer is a subagent on Claude Opus.

You are implementing one piece of a planned change in TScert, a verifier for
TypeScript whose single forward pass is proved sound in Lean 4. Work in the
git worktree `<worktree>` on the branch `<branch>` (it sits on `<base>`,
which must not be rewritten). Read CLAUDE.md there first, then
[the parity skill](SKILL.md): its section "Decisions that bind every design"
binds you.

## Rules

- Create nothing under `~/GitHub/`. Work only in your worktree. Scratch goes
  under `<scratch>`; keep `handover.md` there, current after every commit
  (what is done, what is next, anything a successor needs), and delete other
  scratch when done.
- Do not push. Do not run `git stash` or `pkill`, and do not kill processes
  you did not start.
- Each commit is a green, buildable step with a commit record in the
  repository's format (`.claude/skills/review/SKILL.md`; the hook is
  `bin/git_hooks/commit_record.sh`). Commit often, so that a successor can
  continue if you are cut off.
- Lean: no `sorry`, no axioms, no warnings. Run Lake only as
  `cd lean && lake build ...`; never two builds at once in one worktree;
  build the changed module while iterating.
- Tests: you do not run `make test`, the pretext tier or cost measurements.
  Your gates are `<gates>`. Every command has a limit near its expected
  duration (a build at most 10 minutes, a pattern of cases at most 5); a
  wait you start must end by itself.
- No special cases, no flags, no second mechanism kept beside the first.
  Statements are the notes': cite the note's definition or rule in each new
  definition's documentation comment.
- Decide by principle and do not ask unless truly blocked. If an obligation
  is false or needs a different statement, stop and report it precisely;
  never weaken it silently.

## The piece

Design: `<design section>`. Your files: `<files>`. Files of other
implementers are read, not edited; a mechanical edit that a signature change
forces is listed in your handover.

`<work>`

The headline theorems (`PassUnit.mode8Accepted_sound`,
`passUnitVerdict_sound`, `run_sound_single_pass`) keep their statements, and
`lean/Verification/Tests/AxiomCheck.lean` stays clean. Documents that
describe what you change are updated in the same commit. A change of what is
assumed of the host is named in the commit's `Trust` trailer.

## Report

Your final message, short, numbers first: the commits; the statements added,
changed and removed; any difference from the design and why; verdicts that
changed, each with its cause; each gate with its actual outcome, and what
was not run; what is left, with the exact next obligation.
