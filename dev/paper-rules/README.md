# The paper-rules prototype

The prototype applies the rules of
[An effect language for TScert](../../docs/drafts/effect-languages.md) to
TypeScript sources, on top of the ordinary verifier. Its design and why it
is a prototype are in [the mode's draft](../../docs/drafts/paper-rules-mode.md);
the process it follows is AGENTS.md, "Experimental rules: a lighter process".

## What runs

- `dev/paper-annotations.mts` reads a source's paper annotations into a side
  file: each function's effect variables and bounds (`AtMost<{…}>`), each
  call's instance (`f<{…}>(…)`), each callback's effect read from its
  body, and the `paperAssume` statements.
- The ordinary stages build the request, as `make check` does.
- `lean/PaperRulesPrototype.lean`, the `paper-rules-prototype` executable,
  runs the ordinary pass with one extra checker layer (Bound, Anch, the
  meet, Inst's conclusion at walker calls). At every step but a call of a
  slot, the layer's step and its normal effect are the ordinary checker's,
  so such a step keeps the facts it does not name as in the ordinary pass.
  Its soundness is the axiom `paperKeptFactsSurvive`; every verdict it
  supports names it.
- `dev/paper-rules.mts` drives the three and prints the ordinary verdict and
  the prototype's per unit.

## Commands

```bash
node dev/paper-rules.mts dev/paper-rules/walk.ts --project dev/paper-rules
```

```bash
node dev/paper-rules.mts --check dev/paper-rules/expected.json
```

```bash
node dev/paper-rules.mts --check dev/paper-rules/pretext/expected.json
```

`--check` runs every file an expectation set names and fails on any
verdict that differs from the recorded one. Both sets pass on every commit.
Build first: `(cd lean && lake build verifier paper-rules-prototype)` and
`make build-runner`.

## The examples

- `walk.ts`: the paper's walk, with `sumAndTrace` accepted and
  `sumAndAlias` refused.
- `w1.ts`, `w1-walkers.ts`, `w1-snapshot.ts`: a reduced Pretext walker under a
  declared-reach bound, with positive and negative callers and walkers.
- `claims.ts`: a caller's claim about its callback, checked against the
  callback's body.
- `inst-effect.ts`: the caller's facts kept across a walker call.
- `fresh-at-call.ts`: an instance's root the caller allocates, returned or
  stored after the call, accepted; stored before it, after it in a loop
  enclosing it, or by a function run before it, refused.
- `repro-351.ts`: the loop-head pattern of issue #351, fixed in the verifier
  by #353: accepted, with its two refused variants.
- `repro-364.ts`: issue #364, a bounded walker whose loop needs loop-head
  settling (`lackingAt`): accepted once the diagnosing walk runs with the
  checker layer, with an unsafe unbounded variant refused.
- `repro-365.ts`: issue #365, a cursor's grapheme index, which no clause
  bounds by the length of its segment's list: the read refused, the same
  read with both bounds assumed accepted naming #365, and one assuming only
  the upper bound refused.
- `repro-367.ts`: issue #367, a bound over a local whose changing branch
  always leaves at the next statement: the merge keeps the bound disjoined
  with the changing branch's linear condition and releases it past the exit,
  so every unit verifies.
- `assume-lib.ts`, `assume-importer.ts`: a module holding an assume, and its
  importer, which keeps its ordinary verdict under the prototype.
- `review.ts`, `review-importer.ts`: counterexamples to decisions beyond the
  paper's rules, one per rule, each refused.
- `review2.ts`, `review2-reexporter.ts`, `review2-reimporter.ts`,
  `review2-dir/far.ts`: the second review's counterexamples (a write of an
  array's `length`, `push` of no array, a bound or callback type not read,
  a reassigned parameter, a parameter default, a shadowed callback, calls
  through a re-export or from another directory, a class key in a bound),
  each refused, and an instance after an ordinary type parameter, accepted.
- `module-state.ts`: module-private confined state (`"@state"`,
  `Effects<P, T>`, `Join<E, P>`): positive cases for a confined `let` lazy
  cache, a `Partial<Record<...>>` cache, a nested `WeakMap<P, Map<K, Int32Array>>`
  cache, a walker calling a confined helper, and a forwarding adapter with
  `Join<E, { "@state": "any" }>`; negative controls refusing an escaping
  container, a parameter absorbed into a `let` or `WeakMap` and mutated, an
  escaping nested interior, an exported container, a direct parameter write
  claiming `@state`, a `subarray` stored into a mutated cache, and `@state`
  under an `else: "keep"` bound.

## The Pretext copy

`pretext/src` is Pretext at commit
`0dafecb370638ddc244909cc949efaf85b1efa26` (`~/GitHub/pretext`), with
the prototype's edits and `src/paper.d.ts`, the effect language's
declarations (`Footprint`, `AtMost`, `Effects`, `Join`), a declaration file
so that their effect parameters, which their bodies do not name, are no
unused ones to TypeScript. Every edit is marked:

- `// PAPER`: a paper annotation (a bound, an instance, a visitor type's
  `Modifies<E, void>`, the verifier's declarations the instances need);
- `// PAPER: annotation`: a bounds annotation (`@requires`, `@ensures`,
  `@invariant`, `Modifies`) added for the experiment;
- `// PAPER: guard removed`: a `?? missing()` read restored to `x[k]!`;
- `paperAssume(fact, "#N");`: an unsafe assumption of a condition, tracked
  by issue N, which is either a verifier extension or a proof the source
  does not yet give. `paperAssume` is
  declared in the file as a function with an empty body and
  `Modifies<{}, void>`, so the ordinary verifier's call changes nothing; the
  prototype checks the statement as `if (!(fact)) throw "#N";`, so after it
  the pass knows `fact` as on the branch of an `if` where it holds, and
  names the issue in the verdict. It does so in the checked file only: an
  imported module is read as written, the source its interface was
  established over.

The edits against the pin:

```bash
for f in dev/paper-rules/pretext/src/*.ts; do git -C ~/GitHub/pretext show 0dafecb370638ddc244909cc949efaf85b1efa26:src/$(basename $f) | diff - $f; done
```

`pretext/expected.json` records the ordinary and the prototype's verdict of
every function of the copy.
