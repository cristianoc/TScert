# Links at loop heads

A loop head's knowledge forgets that a local holds the value read from a
field. A program that copies a field before a loop and reads through the
copy inside it is refused:

```ts
export function sumVia(h: { xs: number[] }): number {
  const xs = h.xs;
  let s = 0;
  for (let i = 0; i < h.xs.length; i++) s += xs[i]!;   // refused: nothing says xs is h.xs here
  return s;
}
```

Pretext's walkers have this shape (`const { segmentFlags } = prepared`, then
`segmentFlags[i]` in the loop). The prototype's example
`dev/paper-rules/w1-snapshot.ts` reads through the handle instead, marked
`REVERT`, until this is fixed.

## The existing mechanism this extends

A loop head's knowledge is its given knowledge only (`setupGiven`): the
written assertions and the supplied candidates, which are index atoms
(`List IndexAtom`). Nothing is taken from the entry edge (`inDegrees` leaves
out edges into heads). `headExit` checks every incoming edge against the
given knowledge.

```text
at a loop head l:
  given(l) := written(l) ∪ candidates(l)            -- candidates: index atoms only
  for each edge e into l: require knowledge(e) ⊢ given(l)   -- headExit
```

In `sumVia`, the knowledge after `const xs = h.xs` holds the read link
`xs ← h.xs`. No candidate can state it, so the head starts without it, and
`xs[i]` has no bound.

## The change

Candidates may also be read links: `link(y ← x.f)` for a binding `y`
initialised by a read of `x.f` and never reassigned. Lowering proposes it at
each loop head the binding is live across. The existing settle loop keeps it
when every edge into the head entails it, and drops it otherwise. A back edge
entails it when every step of the body keeps the location `x.f`, by the
existing frame check, which decides from each step's effect.

`sumVia`, through the change: the entry edge has the link from the
assignment; the back edge keeps it, since `s += xs[i]` and `i++` write no
field; the head keeps the link, and `i < h.xs.length` bounds `xs[i]`.

- A body that writes `h.xs` fails the back edge, and the link is dropped.
- A call with `Modifies<{ spines: "grow" }, …>` keeps fields, so the link is
  kept.
- A call with `values: "any"` may change `h.xs`, so the link is dropped.

## What this duplicates

The candidates and their settle loop are those of loop-head inference;
[forward facts](forward-facts.md) §1 already lists links among candidate kinds. The
edge check is `headExit`'s. The frame decision is the existing one. The
change is to the candidate type, which about 30 Lean files read (by grep,
not measured further): `recordCandidates`, request hashing, `MemberSettle`,
`HeadDiagnosis`, `setupGiven_get`, `Site.head_written`, and `headExit`'s
list of missing facts.

## Cases

- **Positive:** `sumVia`; the same with a call keeping fields in the loop.
- **Negative, unsafe under Node:** the body sets `h.xs` to a longer array,
  so `xs[i]` reads past the copy's end. Also negative: a call with
  `values: "any"` in the loop.
