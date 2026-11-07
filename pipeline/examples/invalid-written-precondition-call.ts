// A call outside the precondition: `at(xs, xs.length)` reads past the end, so
// `last([1, 2])` returns `undefined` as a `number` (run under Node).

/** @requires safeInteger(i) && 0 <= i && i < xs.length */
function at(xs: number[], i: number): number {
  return xs[i]!;
}

export function last(xs: number[]): number {
  const n = xs.length;
  return at(xs, n);
}
