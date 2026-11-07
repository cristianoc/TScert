// Written preconditions over lengths: `pair` reads `xs[i]` and `xs[i + 1]`
// under `i + 1 < xs.length`, and `both` reads two arrays at one index under
// `xs.length === ys.length`, each with no check. Their callers establish the
// clauses by a comparison with the length and by a test of the two lengths.

/** @requires safeInteger(i) && 0 <= i && i + 1 < xs.length */
function pair(xs: number[], i: number): number {
  return xs[i]! + xs[i + 1]!;
}

/** @requires safeInteger(i) && 0 <= i && i < xs.length && xs.length === ys.length */
function both(xs: number[], ys: number[], i: number): number {
  return xs[i]! * ys[i]!;
}

export function firstPair(xs: number[]): number {
  if (xs.length >= 2) return pair(xs, 0);
  return 0;
}

export function firstProduct(xs: number[], ys: number[]): number {
  if (xs.length === ys.length) {
    if (xs.length > 0) return both(xs, ys, 0);
  }
  return 0;
}
