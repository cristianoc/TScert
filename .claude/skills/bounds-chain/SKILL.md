---
name: bounds-chain
description: Work on pretext's bound rewrites one chain at a time - restore each `x[k] ?? missing()`, guarded write and explicit undefined check of a chain to its original form with the annotations and TScert rules that prove it, keeping 210 of 210 pretext functions verified, merged step by step. Use when the owner asks to continue a chain, start the next one, or resume the bounds work from nothing.
---

# A bounds chain

Pretext verifies whole under TScert in a rewritten form: the fork
`cristianoc/pretext`, branch `tscert-rewrites` (`2b11a4c`), adds 493 bound
rewrites to upstream `0d102a5c`, and its branch `tscert-bounds` is the
annotated pretext that the work moves forward. The work puts them back to their original
form, a chain of functions at a time, each restored site justified by
annotations in pretext and, where TScert lacks a rule, by a rule added to
TScert. All 210 functions verify after every step.

A chain is a function that builds a structure, and every function reading
it, wherever they are. A chain is finished when all its rewrites are back;
a partial chain is reported as partial, with each site left and its exact
refusal.

| Chain | From | Through |
| --- | --- | --- |
| 1 | `analyzeText` (`src/analysis.ts`) | `measureAnalysis`, `getFollowingSpaceTail`, `getJoinedNarrowing`, `addKanaKerning`, `addIdeographicSpaceHangs` (`src/prepare.ts`) and their callers |
| 2 | the prepared handle (`src/prepare.ts`) | its readers in `src/line-break.ts` |
| 3 | the rich-inline flow (`src/rich-inline.ts`) | its readers |

## Where everything lives

One branch on each side, kept in sync; GitHub holds the whole state, and a
local checkout or worktree is only a copy of it.

- **TScert**, `cristianoc/TScert`: the line `single-pass`. Work lands on it
  through short-lived pull requests, each branch deleted when it merges.
  A chain's state, its sites left and their blockers, is its row of the
  [status table](../../../WORK.md#status).
- **Pretext**, the fork `cristianoc/pretext`: `tscert-bounds`, the
  annotated pretext, one commit per step, its message naming the sites
  and the functions checked. `tscert-rewrites` is its base, the rewritten
  pretext, and is not worked on. Nothing goes to `chenglou/pretext`.
- **In sync**: TScert's CI checks pretext at the tip of `tscert-bounds`
  (`PRETEXT_COMMIT` in [ci.yml](../../../.github/workflows/ci.yml)), and
  [the tier's record](../../../tests/pretext-tier-expected.json) holds
  that commit alone. A step that commits to `tscert-bounds` moves both in
  one TScert pull request, with any TScert change the step needs.

No other branch is made on either side: a worktree for a step is made on
these branches, outside `~/GitHub`, and removed when the step lands.

`tscert-bounds` differs from upstream `0d102a5c` in five kinds of change,
and in nothing else:

1. **A bound check**: `x[k] ?? missing()`, a local followed by
   `if (v === undefined) throw new RangeError('missing value')`, or an index
   write behind `if ((k & 0x7fffffff) !== k || k > xs.length) throw new
   RangeError('index')`, with `missing` in `src/checked.ts`. The work
   restores each to upstream's form.
2. **An annotation** inside pretext: `@requires`, `@ensures`, `@invariant`,
   `@stable`, `Modifies<P, T>`, `Fresh<T>`, the last two declared by
   `src/resolvable.d.ts`, a copy of TScert's `tools/resolvable.d.ts`.
3. **A bounds bug found in upstream**, fixed where it is, under a line
   starting `// bounds bug:` that says what upstream does wrong; each fix
   approved by the owner.
4. **A rewrite into TScert's source fragment**, listed in TScert issue #94
   with the TScert gap whose closing lets it go back to upstream's form.
5. **An annotation on the public API**, on what `src/layout.ts` and
   `src/rich-inline.ts` export, which user code must meet and which is
   assumed, under a line starting `// contract on callers:` that says it in
   plain words, with its row in the trust surface of
   [DESIGN.md](../../../docs/DESIGN.md).

A step commits only changes of these kinds, each kind recognisable in the
source: by its form (1, 2, 4) or by its marker (3, 5).

## Starting from nothing

```sh
git clone https://github.com/cristianoc/TScert.git ~/GitHub/TScert
git clone https://github.com/chenglou/pretext.git ~/GitHub/pretext
git -C ~/GitHub/pretext remote add fork https://github.com/cristianoc/pretext.git
git -C ~/GitHub/pretext fetch fork
git -C ~/GitHub/TScert worktree add -b <step> <dir>/tscert origin/single-pass
git -C ~/GitHub/pretext worktree add --detach <dir>/pretext fork/tscert-bounds
```

Set up the TScert worktree as
[CLAUDE.md](../../../CLAUDE.md#working-in-a-separate-git-worktree) states
(Lean cache, `node_modules`), then `make build`. The pretext worktree
needs no dependencies: the check reads its `tsconfig.json` with
`types: []`.

Check functions of one pretext file, each unit on its own with its
neighbours at their declared signatures (`*` for every unit):

```sh
TSCERT_STEP_LIMIT=300 node dev/check-functions.mts <pretext worktree> analysis.ts analyzeText,segmentAtLineBreaks
```

Under a refused unit the check prints its refusal, located in the source,
with the obligation's summary and the loop-head candidates left out, each
with the edge that does not establish it
([candidates left out](../../../docs/OBLIGATION-DIAGNOSTICS.md#candidates-left-out)).
Read them before forming a hypothesis: a refused read or loop invariant
needs a fact, and an edge listed is where it is not established.

Count the rewrites left, out of 493:

```sh
git -C <pretext worktree> grep -o -E "\?\? missing\(\)|RangeError\('index'\)|RangeError\('missing value'\)" \
  -- 'src/*.ts' 'src/generated/*.ts' ':!src/checked.ts' | wc -l
```

and subtract 42, the markers of `tscert-rewrites` whose operand is not an
index read or write (535 at `2b11a4c`, so 493).

## A step

1. State the relation where the structure is built: an `@ensures` on the
   builder, or on the functions building its parts.
2. Add the `@requires` and loop `@invariant`s the readers need, in call
   order.
3. Restore the rewrites the facts justify, to upstream's form.
4. Check every function touched, and every caller of a function whose
   annotation changed, in any file.
5. When they all verify, commit the step on `tscert-bounds` and push it
   (`git push fork HEAD:tscert-bounds`, a fast-forward). In the step's
   TScert pull request, set `PRETEXT_COMMIT` to that commit and record it
   (`node tests/pretext-tier.mts --pretext <dir>/pretext --update`,
   keeping that commit's record alone).

When TScert refuses what it should accept, close the gap in the step's
TScert pull request, as [CLAUDE.md](../../../CLAUDE.md) requires of any
TScert change:

- a design is drafted and reviewed as
  [designs](../../../CLAUDE.md#designs-start-from-an-existing-mechanism)
  states;
- a rule is general, never shaped to a pretext site;
- a pipeline case, positive and negative, for each rule, the negative run
  under Node; Lean with no `sorry`, axiom or warning; a commit record on
  each commit;
- each commit a self-contained step, mergeable on its own.

An assumption about a library or host function is trust: state it in the
commit record's `Trust`, add its row to the PR's trust list, and leave the
sites it would unblock until the owner approves it.

## The checked-bounds deep dive

[`docs/deep-dives/checked-bounds`](../../../docs/deep-dives/checked-bounds)
presents TScert's arithmetic and bound support conceptually: the kinds of
facts, how they are established and carried, what acceptance guarantees,
and what remains. It states the current conceptual state, in its own
style ([STYLE.md](../../../docs/STYLE.md)).

- A step that changes a concept updates the deck in the same pull
  request. Such a step adds a kind of fact or of rule, a contract form, a
  way facts survive calls or writes, a kind of trust, or a class of
  obligation that remains. The update rewrites the slides that concept
  touches, so the deck reads as if written today.
- A small fix, a new instance of an existing rule, or a count moving adds
  nothing to the deck. Its outcome numbers are measurements with their
  commit, refreshed when a chain finishes.
- The deck keeps its structure and voice; it never gains a history or a
  list of changes. A revised deck reaches the owner marked since its
  approved version
  ([a revised deck](../../../docs/STYLE.md#a-revised-deck)).

## Testing

Narrow while working: `run-cases.mts <pattern>` for the cases a rule
touches, the Lean module changed, `dev/check-functions.mts` for the pretext
functions touched and their callers. All of pretext, every file with `*`,
before a step's commit when its TScert rule could reach other files. At
most 3 checks at once. No census, no `make test` or full `run-cases.mts`:
CI's `test` job runs `make test` on the PR and again on `single-pass`. It gates no
merge ([how a pull request lands](../../../CLAUDE.md#how-a-pull-request-lands)),
so a step is reported as tested only with the `test` run it names.

## Stacked pull requests

A pull request lands by rebase and merge
([how a pull request lands](../../../CLAUDE.md#how-a-pull-request-lands)),
never by a merge commit or a squash that drops commit records, so every
branch stays linear on top of its parent.

- A branch that depends on another unmerged branch is based on it, and its
  pull request's base is that branch. A native GitHub stack
  (`gh stack link <bottom> <next> …`, bottom to top) shows them as one; a
  stack merges only by squash here, so unstack it (`gh stack unstack <n>`)
  before landing its bottom pull request. Branches that share a parent
  but not each other (two children of one branch) are separate pull
  requests on that parent, never one stack.
- Before every push, check each pair:
  `git merge-base --is-ancestor <parent> <child>`, from `origin/single-pass`
  upward. A pair that fails shows the parent's commits in the child's pull
  request.
- When a parent moves, rebase each child onto it, from the bottom up:
  `git rebase --onto <parent> <parent's old head> <child>`, then push with
  `--force-with-lease`. When the parent lands on `single-pass`, rebase the
  child onto `origin/single-pass` the same way and
  `gh pr edit <child PR> --base single-pass`.
- A branch that already contains merge commits is replayed onto its base
  (`git rebase -X theirs <base>`), then one commit restores the tested
  tree (`git checkout <tested head> -- .`, removing files that tree lacks),
  so the landed tree is byte-identical to the one CI tested.
- GitHub refuses to rebase-merge a pull request of more than about 100
  commits ("This branch can't be rebased"). Such a branch, already linear
  on `single-pass`, lands by fast-forwarding `single-pass` once its checks
  pass, as [the parity skill](../parity/SKILL.md) states.

## Merging

A step lands when its TScert pull request is green: `render`, `test`, and
`pretext` at the new pin. Its trust, if any, is reviewed by the owner
first. Each push to the fork needs the owner's instruction.

## Report

Numbers first: the chain's rewrites restored out of its total, pretext
functions verified out of 210, rewrites left out of 493. Then the
annotations added with what they state, the TScert commits with their
cases, the trust stated plainly, and each site left with its exact
refusal. Plain words; no either-or questions.
