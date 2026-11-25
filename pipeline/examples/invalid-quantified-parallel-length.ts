// Unsafe counterpart to parallel-array element length: `xs[j].length <= ys[j].length + 1`
// lets `ys[j]` be one element shorter than `xs[j]`, so reading `e[g]!` at the
// last index of `row` reads `undefined` at `number` (`NaN` under Node).

/** @requires safeInteger(i) && 0 <= i && i < xs.length
 *  @requires ys === null || xs.length <= ys.length
 *  @requires ys === null || forall j in xs: xs[j] === null || ys[j] === null || xs[j].length <= ys[j].length + 1 */
export function sumShortExtras(xs: (number[] | null)[], ys: (number[] | null)[] | null, i: number): number {
  const row = xs[i]!;
  if (row === null) return 0;
  const e = ys === null ? null : ys[i]!;
  let total = 0;
  for (let g = 0; g < row.length; g++) {
    total += row[g]! + (e === null ? 0 : e[g]!);
  }
  return total;
}
