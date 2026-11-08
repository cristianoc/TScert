// A module exporting functions that state preconditions, which the
// precondition import examples import. Each call inside the analyzed
// sources establishes the clause; a caller outside them is trusted to.

/** @requires safeInteger(i) && 0 <= i && i < xs.length */
export function at(xs: number[], i: number): number {
  return xs[i]!;
}

/** @requires safeInteger(i) && 0 <= i && i + 1 < xs.length */
export function pairSum(xs: number[], i: number): number {
  return at(xs, i) + at(xs, i + 1);
}
