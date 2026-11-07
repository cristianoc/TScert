// A body relying on more than its precondition states: the clause bounds no
// index, so `at([1], 5)` reads `undefined` as a `number` (run under Node).

/** @requires safeInteger(i) && 0 <= i */
function at(xs: number[], i: number): number {
  return xs[i]!;
}

export function first(xs: number[]): number {
  return at(xs, 0);
}
