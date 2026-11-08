// Preconditions over lengths: `pair` reads `xs[i]` and `xs[i + 1]`
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

// In a loop: the test's equality is kept by each call of `both`, whose
// footprint keeps the heap, so every iteration's call establishes it.
export function dot(xs: number[], ys: number[]): number {
  if (xs.length !== ys.length) throw new Error("lengths differ");
  let s = 0;
  for (let j = 0; j < xs.length; j++) s = s + both(xs, ys, j);
  return s;
}

// A literal index asserted present, read below the length its clause states.
/** @requires 2 <= xs.length */
function second(xs: number[]): number {
  return xs[1]!;
}

export function secondOf(xs: number[]): number {
  if (xs.length >= 2) return second(xs);
  return 0;
}
