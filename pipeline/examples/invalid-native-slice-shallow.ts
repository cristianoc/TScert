// The zero-argument `slice()` copies the receiver's values, not the arrays
// they refer to: the copy's elements are the receiver's elements. Emptying the
// copy's row empties the receiver's, so `row[0]` is absent under Node
// (`headAfterRowPop([[1]], 0)` throws a TypeError).
/** @requires safeInteger(k) && 0 <= k && k < xs.length
 *  @requires forall i in xs: xs[i] === null || 1 <= xs[i].length */
export function headAfterRowPop(xs: (number[] | null)[], k: number): string {
  const copy = xs.slice();
  const shared = copy[k] ?? null;
  if (shared !== null) shared.pop();
  const row = xs[k] ?? null;
  if (row === null) return "";
  return row[0]!.toFixed(0);
}
