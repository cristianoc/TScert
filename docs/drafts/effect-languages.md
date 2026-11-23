# Effect languages

[Read the paper (PDF)](effect-languages-note/effect-languages.pdf) ·
[LaTeX source](effect-languages-note/note.tex)

The paper states the effect rules once, over any effect language with four
properties, and describes TScert's footprints as one such language,
$`\mathcal L_0`$. It then proposes $`\mathcal L_1`$, which adds regions at
a closure's captures, effect variables bounded by a support, anchored
effects and reach through declared keys, and derives Pretext's line-walker
patterns in it. $`\mathcal L_1`$ has no implementation and no proof.

## The existing mechanism this extends

The mechanism is the tolerant frame at a call
([footprints](../FOOTPRINTS.md#support-and-respect),
[the Tolerant frames note](../REFERENCES.md#the-tolerant-frames-note)).
Read from `Footprints.respects`, `Footprints.Post` and the call's effect
(`CallEffects.Effect`):

```text
at a call y = f(x⃗):
  Φ := the effect of f's signature, its parameters replaced by x⃗
  for each fact F known before the call, with support S:
    keep F if  ∀ (r:δ) ∈ S. ∀ (r':γ) ∈ Φ.  γ ⊑ δ  or  q(r, r')
```

Here `q` is the separation query, sound at the call's state. A callback's
type states a closed effect, `Modifies<{ values: c₁; spines: c₂ }, T>`, so
`Φ` is the same for every closure the callback parameter receives.

**Example, as it is.** In

```ts
type Visitor = (i: number) => Modifies<{ values: "any"; spines: "grow" }, void>;
export function walk(xs: number[], visit: Visitor): number {
  const c = { i: 0 };
  let sum = 0;
  /** @invariant safeInteger(c.i) && 0 <= c.i */
  while (c.i < xs.length) { visit(c.i); sum += xs[c.i]!; c.i++; }
  return sum;
}
```

the fact `c.i < xs.length` has support `{c.i: keep, xs.spine: grow}`. At
`visit(c.i)`, `Φ = {values: any, spines: grow}`. The pair `(c.i: keep)`
and the entry `(values: any)` fail both alternatives, so the fact is
dropped and `walk` is refused at `xs[c.i]`.

**The proposed change.** A signature quantifies over its callback's effect
and bounds it by a support: `walk<E extends Respects<{ "xs[*]": "keep" }>>(xs, visit: Visitor<E>): Modifies<E, number>`.
At the visit, `Φ = E`. A pair whose region the constraint covers meets the
first alternative through the constraint (rule Var-Resp). A pair whose
region the body allocated is disjoint from `E`, since `E` ranges over
effects anchored at the call of `walk` (rule Fresh-Anch). Each caller
writes its closure's effect, rooted at its captures, and proves the
constraint at the call with the same respect check (rule Inst).

**Example, through the change.** At `visit(c.i)`, `(c.i: keep)` is
disjoint from `E` by Fresh-Anch, and `(xs.spine: grow)` holds by
Var-Resp, since the constraint keeps `xs.spine`. The read is in bounds. In
`sumAndTrace`, `E := {visited.spine: extend}` meets the constraint because
the fresh `visited` is apart from `xs`. In `sumAndAlias`, `visited` is
`xs`, and the call is refused.

## What this duplicates

- **Effects and their action** are `Footprints.Post` over the regions of
  `Footprints.Region`; the extension adds region forms and effect
  variables, and keeps the action.
- **Respect and separation** are `Footprints.respects` and the separation
  query; the constraint check at a call is that check, and disjointness by
  keys is `Footprints.Region.apart_of_keys`.
- **Rigidity and rebasing** are the note's; anchoring is a property of an
  effect's regions that the rigid paths establish.
- **Closure effects** are checked by the existing function rule, at
  parameters and captures. The inferred demand of
  [pull request 338](https://github.com/cristianoc/TScert/pull/338) is a
  written constraint here, and its caller check is rule Inst.
