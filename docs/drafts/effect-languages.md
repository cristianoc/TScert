# An effect language for TScert

[Read the paper (PDF)](effect-languages-note/effect-languages.pdf) ·
[LaTeX source](effect-languages-note/note.tex)

The paper proposes one effect language for TScert. An effect is a
relation between the heap before a step and the heap after it, with an
explicit `else` for the locations its entries do not cover, so the facts a
step must preserve are effects too and every check is inclusion. The
language has regions at a closure's captures, effect variables bounded by
effects, and reach through declared keys; the paper derives Pretext's
line-walker patterns in it. TScert's footprints today are a fragment,
$`\mathcal L_0`$, which a section maps to the language. The language
beyond $`\mathcal L_0`$ has no implementation and no proof.

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

the fact `c.i < xs.length` survives every step bounded by
`{c.i: keep, xs.spine: grow; else: any}`. At `visit(c.i)`,
`Φ = {values: any, spines: grow}`. The entry `values: any` covers `c.i`,
so `Φ` is not included in that effect, the fact is dropped and `walk` is
refused at `xs[c.i]`.

**The proposed change.** A signature quantifies over its callback's effect
and bounds it by an effect:
`walk<E extends AtMost<{ "xs[*]": "keep"; else: "any" }>>(xs, visit: Visitor<E>): Modifies<E, number>`.
At the visit, `Φ = E`. Inside `walk`, `E` is included in its bound (rule
Bound) and in `{old: any}`, the locations that existed at the call (rule
Anch), so in their meet. Each caller writes its closure's effect, rooted at
its captures, and proves the bound at the call by the same inclusion (rule
Inst).

**Example, through the change.** At `visit(c.i)`, the meet keeps `c.i`,
which is not `old`, and keeps the spine of `xs`, so it is included in
`{c.i: keep, xs.spine: grow; else: any}` and the read is in bounds. In
`sumAndTrace`, `E := {visited.spine: extend}` is within the bound because
the fresh `visited` is apart from `xs`. In `sumAndAlias`, `visited` is
`xs`, and the call is refused.

## What this duplicates

- **Effects and their action** are `Footprints.Post` over the regions of
  `Footprints.Region`; the extension adds region forms and effect
  variables, and keeps the action.
- **Inclusion and separation** are `Footprints.respects` and the
  separation query: an effect with `else: keep` (`Post`) included in one
  with `else: any` (`Supported`); the bound check at a call is that check,
  and disjointness by keys is `Footprints.Region.apart_of_keys`.
- **Rigidity and rebasing** are the note's; anchoring is a property of an
  effect's regions that the rigid paths establish.
- **Closure effects** are checked by the existing function rule, at
  parameters and captures. The inferred demand of
  [pull request 338](https://github.com/cristianoc/TScert/pull/338) is a
  written bound here, and its caller check is rule Inst.
