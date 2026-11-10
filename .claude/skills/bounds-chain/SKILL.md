---
name: bounds-chain
description: Work on pretext's bound rewrites one chain at a time - restore each `x[k] ?? missing()`, guarded write and explicit undefined check of a chain to its original form with the annotations and TScert rules that prove it, keeping 210 of 210 pretext functions verified, merged step by step. Use when the owner asks to continue a chain, start the next one, or resume the bounds work from nothing.
---

# A bounds chain

Pretext verifies whole under TScert in a rewritten form: the fork
`cristianoc/pretext`, branch `tscert-rewrites` (`2b11a4c`), adds 501 bound
rewrites to upstream `0d102a5c`. The work puts them back to their original
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

GitHub holds the whole state; a local checkout is only a copy of it.

- **TScert**, `cristianoc/TScert`:
  - `main` holds the checked bound annotations, the base of the chains.
  - `chainN-tscert`, one PR per chain into `main` (chain 1:
    `chain1-tscert`, PR #129): the TScert rules of chain N.
    Its description holds the table pairing each pretext commit with
    the TScert commit it needs, and the trust under review.
  - The chain's state, its sites left and their blockers, is its row of
    the [status table](../../../WORK.md#status) on `chainN-tscert`.
- **Pretext**, the fork `cristianoc/pretext`:
  - `tscert-rewrites`, PR cristianoc/pretext#1 into the fork's `main`:
    the rewritten baseline, one commit.
  - `tscert-bounds`, PR cristianoc/pretext#2 into `tscert-rewrites`,
    stacked on pretext#1:
    every restored site, one commit per step, its message naming the sites
    and the functions checked.
  - Nothing goes to `chenglou/pretext`.

Local copies: `~/GitHub/TScert` holds the TScert branches, each worked in
a worktree of that repository; `~/GitHub/pretext` holds `tscert-bounds`,
tracking `fork/tscert-bounds`, worked in a worktree of that repository.

## Starting from nothing

```sh
git clone https://github.com/cristianoc/TScert.git ~/GitHub/TScert
git clone https://github.com/chenglou/pretext.git ~/GitHub/pretext
git -C ~/GitHub/pretext remote add fork https://github.com/cristianoc/pretext.git
git -C ~/GitHub/pretext fetch fork
git -C ~/GitHub/TScert worktree add <dir>/tscert chain1-tscert
git -C ~/GitHub/pretext worktree add -b tscert-bounds <dir>/pretext fork/tscert-bounds
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
then every place where the unit's proposal drops facts, with the facts and
what dropped them
([where a proposal drops facts](../../../docs/OBLIGATION-DIAGNOSTICS.md#where-a-proposal-drops-facts)).
Read that list before forming a hypothesis: a refused read or loop
invariant needs a fact, and the list names each statement past which that
fact is no longer proposed. `--explain` as a fourth argument prints the
list for verified units too, with what makes a function's inferred
footprint `store: any`.

Count the rewrites left, out of 501:

```sh
git -C <pretext worktree> grep -o -E "\?\? missing\(\)|RangeError\('index'\)|RangeError\('missing value'\)" \
  -- 'src/*.ts' 'src/generated/*.ts' ':!src/checked.ts' | wc -l
```

and subtract 34, the markers of `tscert-rewrites` that check something
other than a bound (535 at `2b11a4c`, so 501).

## A step

1. State the relation where the structure is built: an `@ensures` on the
   builder, or on the functions building its parts.
2. Add the `@requires` and loop `@invariant`s the readers need, in call
   order.
3. Restore the rewrites the facts justify, to upstream's form.
4. Check every function touched, and every caller of a function whose
   annotation changed, in any file.
5. Commit the step on `tscert-bounds` when they all verify, and add its
   row to the PR's table.

When TScert refuses what it should accept, close the gap in
`chainN-tscert`, as [CLAUDE.md](../../../CLAUDE.md) requires of any
TScert change:

- a design starts from the [existing mechanism](../../../docs/DESIGN.md#general-mechanisms)
  it extends; a new one is drafted in `docs/drafts/` and reviewed by
  Astra before it is built;
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
CI's `test` job runs `make test` on the PR and again on `main`. It gates no
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
  `git merge-base --is-ancestor <parent> <child>`, from `origin/main`
  upward. A pair that fails shows the parent's commits in the child's pull
  request.
- When a parent moves, rebase each child onto it, from the bottom up:
  `git rebase --onto <parent> <parent's old head> <child>`, then push with
  `--force-with-lease`. When the parent lands on `main`, rebase the child
  onto `origin/main` the same way and `gh pr edit <child PR> --base main`.
- A branch that already contains merge commits is replayed onto its base
  (`git rebase -X theirs <base>`), then one commit restores the tested
  tree (`git checkout <tested head> -- .`, removing files that tree lacks),
  so the landed tree is byte-identical to the one CI tested.
- GitHub refuses to rebase-merge a pull request of more than about 100
  commits ("This branch can't be rebased"). Such a branch, already linear
  on `main`, lands by fast-forwarding `main`, which only the owner, on the
  ruleset's bypass list, can push.

## Merging

The green steps of `chainN-tscert` land once the owner reviewed their
trust; later steps continue on the branch. When TScert steps land, the
pretext steps they justify fold into the single commit of
`tscert-rewrites`, and `tscert-bounds` is rebased on it. Each push needs
the owner's instruction.

## Report

Numbers first: the chain's rewrites restored out of its total, pretext
functions verified out of 210, rewrites left out of 501. Then the
annotations added with what they state, the TScert commits with their
cases, the trust stated plainly, and each site left with its exact
refusal. Plain words; no either-or questions.
