// Positive case: a transparent generic wrapper alias (`type Tagged<Tag, T> = T`)
// unfolds to `T` when collecting type invariants (`invariantsNamed`), so both
// producers and consumers enforce and read `T`'s `@invariant`.

type Tagged<_Tag, T> = T;

/** @invariant this.xs.length === this.ys.length */
type EqualPair = {
  xs: number[];
  ys: number[];
};

export function makeTaggedPair(
  a: number,
  b: number,
): Tagged<"pair", EqualPair> {
  return { xs: [a, b], ys: [b, a] };
}

export function sumTaggedPair(p: Tagged<"pair", EqualPair>): number {
  let total = 0;
  /** @invariant p.xs.length === p.ys.length && safeInteger(i) && 0 <= i && i <= p.xs.length */
  for (let i = 0; i < p.xs.length; i++) total += p.xs[i]! + p.ys[i]!;
  return total;
}

export function roundTripTaggedPair(a: number, b: number): number {
  const p = makeTaggedPair(a, b);
  return sumTaggedPair(p);
}
