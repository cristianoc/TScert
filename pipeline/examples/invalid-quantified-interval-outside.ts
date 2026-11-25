// Negative control for issue #396: an interval quantifier `forall lo <= j < hi`
// does not bound index `lo - 1` below the lower bound.
// Unsafe under Node: `readBeforeLowerBound([99, 0], [42], 1, 2)` reads `table[99]`
// (`undefined` at `number`), returning `NaN`.
/**
 * @requires safeInteger(lo) && safeInteger(hi)
 * @requires 1 <= lo && lo < hi && hi <= xs.length
 * @requires forall lo <= j < hi of xs: safeInteger(xs[j]) && 0 <= xs[j] && xs[j] < table.length
 */
export function readBeforeLowerBound(
  xs: number[],
  table: number[],
  lo: number,
  hi: number,
): number {
  const idx = xs[lo - 1]!;
  return table[idx]! + 1;
}
