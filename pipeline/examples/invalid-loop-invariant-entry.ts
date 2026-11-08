// A loop invariant its entry does not establish: `j` starts at 2, above
// `2 * i` at `i = 0`, so the head refuses the entry edge. The read it would
// bound runs past the end (run under Node: `shifted([1, 1], [1, 1, 1, 1])`
// reads `ys[4]`, `undefined` at `number`, and returns `NaN`).

/** @requires 2 * xs.length <= ys.length */
export function shifted(xs: number[], ys: number[]): number {
  let j = 2;
  let s = 0;
  /** @invariant safeInteger(i) && safeInteger(j) && 0 <= j && j <= 2 * i */
  for (let i = 0; i < xs.length; i++) {
    s += xs[i]! * ys[j]!;
    j += 2;
  }
  return s;
}
