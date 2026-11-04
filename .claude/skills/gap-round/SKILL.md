---
name: gap-round
description: One round of gap work on TScert's own code, run on main without stops - the census, reasons confirmed from its units' refusals, a case example for each reason no case shows, then the next 10 cases by priority, at most 5 agents at a time, merged locally, then the census and the deck rebuild. Use when the owner asks for a gap round, for "the next 10 cases", or to "follow the process" on gaps.
---

# A gap round

The policy lives in CLAUDE.md, under
[choosing the gap cases to work on](../../../CLAUDE.md#choosing-the-gap-cases-to-work-on),
and in the routes of
[deciding what a refusal calls for](../../../docs/SOURCE-REWRITES.md#deciding-what-a-refusal-of-tscerts-code-calls-for).
This skill is the order in which a round runs them. The owner's request
starts the round, and the round runs to the end without asking.

- Commits and local merges on main need no approval. A push needs the
  owner's instruction for that push.
- A case blocked by a library or host function TScert does not model yet
  gets a model of that function, written and checked against the policy
  by Astra. The owner reviews the model before the push. A question goes
  to the owner only when no principle decides it. It then takes one or two
  sentences, naming the missing principle.
- Every case of the round is closed: it verifies, as written or in the
  equivalent form TScert's code takes, with the avoided form recorded. A
  case is a negative case only where its program is unsafe, shown under
  Node.
- Heavy runs (`make suite`, `make test`, `make census`, `run-cases.mts`
  with no pattern) take the lock `<scratch>/heavy.lock`, where `<scratch>`
  is the session's scratchpad. One census runs at a time.

## 1. The census

On main, after `df -h` shows room, run under the lock:

```sh
make census
node dev/census.mts refusals <record>
```

The census prints the record's path. `refusals` groups the refused
functions by the blocker their unit's refusal names and the source text it
refuses, with each group's functions, statements and weight.

## 2. The reasons, confirmed from the record

Read the record and its refusals, not a new run. For each of the top
reasons, in the order of step 4:

- Read the refusal at its site in the source file, at the span the
  record gives for the unit's refusal.
- Confirm that the reason names one construct.
- Split a reason that stands for several causes (a failed search, an
  expression with no claimed type) by the functions it meets.
- Mark the sites where TScert's own code discards what it knew. Those are
  repaired in the code.

Write the confirmed ranking to `<scratch>/round/ranking.md`: the reason,
statements, functions, sites, the case showing it, and repair sites.

## 3. A case example for each reason no case shows

For each confirmed reason with no pipeline case, add the case: the
smallest source with that refusal. Its header names the census functions
it stands for, and `pipeline/cases.mts` gets its entry as a gap. Check
that the case reproduces the census refusal (`run-cases.mts <name>`).
Commit the cases, one record. These are the round's
step-1 cases.

## 4. The next 10 cases, at most 5 agents at a time

Take the 10 open cases of the ranking, in its order: by the weight
`census.mts refusals` gives each reason, each function it blocks counting
10 / (10 + its statements). For each, start a background agent in its own worktree (`isolation: "worktree"`)
with [brief.md](brief.md), the case's name, its reason and its sites
from `ranking.md`. When an agent finishes, start the next case, keeping
at most 5 running.

When an agent reports:

1. Review the branch. For new nontrivial rules, models of external code,
   or changes of trust, Astra reviews `git diff main...HEAD` with the goal
   stated (see the memories on Astra). Its first question is whether the
   change is an instance of an existing mechanism, and which, or what it
   duplicates ([designs start from an existing
   mechanism](../../../CLAUDE.md#designs-start-from-an-existing-mechanism)).
   On blocking findings, Astra
   implements its fixes and a fresh Astra reviews the result.
2. Check that the change is general and principled, and that it does not
   restrict TScert to fit the mechanism.
3. Merge onto main (fast-forward or cherry-pick). Keep both sides of an
   append conflict in SOURCE-REWRITES.md or WORK.md. Then build on main.

## 5. Verify main, then the census

After the last merge, run under the lock:

- `make suite` and `make test` on main. Each must pass.
- `make census`, the verified census.

Compare with the previous census on main:

```sh
node dev/census.mts report <before> <after>
```

Report every lost function as a regression. Fix it before the round ends,
or report it to the owner as a regression with its cause. Record the
movement in WORK.md's status table and commit it.

## 6. The deck

Rebuild the
[gap-priorities deep dive](../../../docs/deep-dives/gap-priorities/deck.mts)
from the census of the new main (steps 1 and 2 again on its record). Mark it
since the version last approved
([a revised deck](../../../docs/STYLE.md#a-revised-deck)). It is written
for a reader with zero context and reviewed against the sources before it
reaches the owner
([writing and checking a deck](../../../docs/STYLE.md#writing-and-checking-a-deck)).

## The report

Lead with the number: verified functions before → after (total, and of
the original 499), with the functions lost and gained. Then one line per
case: verified, answered by a route (which one), or open with what it
needs. Then any model of external code the owner reviews before the push,
and the state of the push.
