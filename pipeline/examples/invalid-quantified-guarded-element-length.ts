// Unsafe counterpart to quantified-guarded-element-length: `0 <= xs[i].length`
// admits an empty inner array, so `row[row.length - 1]!` reads index `-1`
// (`undefined` at `number`, returning `NaN` under Node).

/** @requires safeInteger(i) && 0 <= i && i < xs.length
 *  @requires forall j in xs: xs[j] === null || 0 <= xs[j].length */
export function lastOrZero(xs: (number[] | null)[], i: number): number {
  const row = xs[i];
  if (row === undefined || row === null) return 0;
  return row[row.length - 1]! + 1;
}
