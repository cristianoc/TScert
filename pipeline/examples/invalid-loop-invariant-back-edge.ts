// A loop invariant its back edge does not establish: `j += 3` leaves
// `j <= 2 * i` false on the next iteration, so the head refuses the edge.
// The read it would bound runs past the end (run under Node:
// `everyThird([1, 1, 1], [1, 1, 1, 1, 1, 1])` reads `ys[6]`, `undefined` at
// `number`, and returns `NaN`).

/** @requires 2 * xs.length <= ys.length */
export function everyThird(xs: number[], ys: number[]): number {
  let j = 0;
  let s = 0;
  /** @invariant safeInteger(i) && safeInteger(j) && 0 <= j && j <= 2 * i */
  for (let i = 0; i < xs.length; i++) {
    s += xs[i]! * ys[j]!;
    j += 3;
  }
  return s;
}
