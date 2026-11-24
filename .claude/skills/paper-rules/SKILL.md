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
- **Branch**: work lands on `single-pass` via pull requests.
- **Issues for unsafe assumes**: each `paperAssume` names its tracking issue;
  the live list of open assumes lives in the [WORK.md](../../../WORK.md#status)
  row.

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

## Unification guardrails

The priority is Pretext coverage, while keeping the prototype ready to fold
into the proved `SinglePass` verifier without unnecessary reconciliation debt:

- **Thin call-framing layer only.** `lean/PaperRulesPrototype.lean` stays
  strictly a `SinglePass.PassLayer` for the four paper rules (`Bound`, `Anch`,
  `Meet`, `Inst`) and `paperAssume`. General reasoning improvements (merges,
  loop-head invariants, arithmetic, local-object confinement, `@ensures`
  propagation) land in the proved `SinglePass` pass rather than as workarounds
  in the prototype layer.
- **Shared region vocabulary (`Footprints.Region`).** Every region form read by
  `PaperRulesPrototype.lean` maps to `Verification.Semantics.Footprints.Region`
  or its type-directed declared-reach expansion. Any new region form Pretext
  requires (such as map or `WeakMap` entries for W5) is introduced in
  `Footprints.Region` and proved in `Model.lean` first, rather than as a
  prototype-only string key.
- **Purely type-directed declared reach (`Acc(T)`).**
  `dev/paper-annotations.mts` computes declared reach strictly from `T`'s
  declared TypeScript type (Definition 4 of the effect-language paper), with no
  per-function overrides or runtime-only shortcuts, so Lean can verify `Acc(T)`
  directly against `Types` when unifying.
- **Single soundness seam (`Rules.lean`).** Every rule change keeps
  `Rules.lean`, `Model.lean`, `PaperRulesPrototype.lean`, and the paper in
  lockstep, so eventual unification consists of instantiating `Rules.Semantics`
  with TScert's `TolerantFrames` semantics (reusing `LocalConfinement` and
  `respects`), moving annotation parsing into `tools/type-graph.mts` and
  `EffectCodec.lean`, and deleting `paperKeptFactsSurvive`.

## How the work runs

- Work happens on a branch off `single-pass` in an isolated worktree outside
  `~/GitHub` (never in `~/GitHub`). Copy `lean/.lake` and the `node_modules`
  from the main checkout (AGENTS.md, "Working in a separate git worktree").
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
