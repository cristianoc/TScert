---
name: paper-rules
description: Continue the effect-language work - the paper "An effect language for TScert", its rules in Lean and their model, and the paper-rules prototype that applies them to Pretext's walkers. Use when the owner asks to resume or continue the paper rules, the prototype, the effect language, or the walkers' guards, from a chat with no context.
---

# The effect language and its prototype

This skill is the context a new chat needs. Read it, then the row
"Pretext's walkers across their visitors" of [WORK.md](../../../WORK.md#status),
then [the prototype's README](../../../dev/paper-rules/README.md).

## The goal

TScert refuses Pretext's line walkers because a walker calls a visitor
between reads, and the visitor's effect is one fixed type for every caller.
The goal is to verify the walkers by writing the visitor's effect down as a
bounded effect variable, without the runtime guards (`?? missing()`) Pretext
carries today:

```ts
type Visitor<E extends Footprint> = (width: number) => Modifies<E, void>
walkLines<E extends AtMost<{ "prepared.**": "keep"; else: "any" }>>(prepared, onLine: Visitor<E>)
walkLines<{ "lines[*]": "extend" }>(p, w => { lines.push(w) })   // accepted
walkLines<{ "lines[*]": "extend" }>(p, w => p.widths.push(0))    // refused
```

## Where things are

- **The paper**: [docs/drafts/effect-languages.md](../../../docs/drafts/effect-languages.md)
  and its LaTeX (`docs/drafts/effect-languages-note/`). One effect language:
  an effect is a relation between heaps with an explicit `else`, bounds are
  effects, every check is inclusion. Section "The effects TScert has" maps
  the existing footprints to it.
- **The rules in Lean**: `lean/Verification/Paper/EffectLanguage/Rules.lean`
  (propositions over a semantics interface) and `Model.lean` (an idealised
  model over the verifier's heaps that proves them).
- **The mode's design and the prototype**:
  [docs/drafts/paper-rules-mode.md](../../../docs/drafts/paper-rules-mode.md),
  [dev/paper-rules/README.md](../../../dev/paper-rules/README.md).
- **The Pretext copy and its verdicts**: `dev/paper-rules/pretext/`.
- **Pull request**: cristianoc/TScert#347 (branch `effect-languages-paper`,
  based on `single-pass`).
- **Issues for unsafe assumes**: each `paperAssume` names one.
  cristianoc/TScert#355 (a callback's call drops the facts over a local
  object) is in use in `dev/paper-rules/repro-355.ts` and the Pretext copy,
  and #365 (no clause bounds the cursor's grapheme index) in
  `dev/paper-rules/repro-365.ts` and the copy; in the copy also #356 (the
  prepared handle's length invariant), #361 (the public line streams'
  `start` cursor), #362 (no `@ensures` of a generic or imported callee),
  #363 (the complex walker's returned cursor) and #364 (the handle's length
  across the walkers' visits); #351 (links at loop heads) was one, fixed by
  #353.

## Standing decisions (the owner's, 2026-11-23)

- **Write effects down, don't infer them.** The inference approach (PRs 337, 338, 342)
  is closed.
- **The prototype and the paper stay in sync.** A change to what the
  prototype decides changes the paper in the same commit (AGENTS.md).
- **The rules are experiments.** They change as applying them to patterns
  shows what the patterns need. A change keeps the rule's statement in
  `Rules.lean`, its proof in `Model.lean`, the prototype's check and the
  paper in one commit (AGENTS.md, "Experimental rules: a lighter process":
  no design draft, no Astra or Fable review for this work).
- **A proved mode was measured and deferred.** It needs arrows whose effect is a
  variable; the change to regions or exit schemas is not local. The
  prototype runs the real pass with one extra layer resting on one named
  axiom, outside the library; at every step but a call of a slot, the
  layer's step and its normal effect are the ordinary checker's.
- **General rules only.** No rule keyed on names, fields or the examples' shapes;
  where the pass's knowledge can't decide the general rule, refuse.
- **Low-risk premises.** Premises such as "allocated in the body" are decided in the
  layer under the axiom, without asking.
- **Gaps of the sound verifier** are not worked around in the code. Write
  `paperAssume(fact, "#N");` where the fact is lost, a self-contained repro,
  and an issue N for a PR that extends the verifier. The issue N tracks
  either a verifier extension or a proof the source does not yet give: an
  invariant is stated, and wherever the source does not establish it, the
  missing fact is assumed naming its issue; the assumes come out in later
  steps.
- **Keep partial progress.** An annotation added for a guard that still
  can't come out stays, with an unsafe assume of its missing fact wherever
  the source does not establish it. Guards come out one at a time, kept
  only if every function of the file still passes, judged on the
  prototype's verdict where an assume is involved. Progress is the number
  of guards removed and the number of assumes left.
- **Tests.** Every behaviour has positive and negative cases recorded in an
  expectation set; each negative says whether the program is unsafe or
  only unprovable.

## How the work runs

- Work happens on the branch of #347 in a worktree under the session's
  scratchpad, never in `~/GitHub`. Copy `lean/.lake` and the
  `node_modules` from the main checkout (AGENTS.md, "Working in a separate
  git worktree").
- Each step is one agent with a narrow brief. It commits locally with
  commit records and does not push. The lead session reruns both
  expectation sets, checks the code for names or shapes, and then pushes.
- Before a push: `node tests/docs.mts`; `(cd lean && lake build
  Verification verifier paper-rules-prototype)` when Lean changed;
  `(cd tools && npx tsc -p tsconfig.json)` and `node tools/unchecked.mts`
  when `dev/` or `tools/` changed; both expectation sets.
- Reports to the owner are short and conceptual, with a small program as
  the example, and say what each result means for verifying Pretext.

## The state

The WORK.md row holds the current state and the next step. Update it in
the commit that changes either.
