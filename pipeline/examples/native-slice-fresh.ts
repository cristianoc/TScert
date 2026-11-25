// The zero-argument `slice()` (SOURCE-CONTRACTS.md, `ArrayProto`) returns a
// fresh array: its spine and element cells are new, and it holds the
// receiver's own values at the same indices, its holes and its length. A
// write to the copy's cell leaves the receiver's element, so the receiver's
// quantified bound still gives `row[0]` (`headAt([[1]], 0)` is "1" under
// Node; were the copy the receiver, `row` would be `[]` and `row[0]` absent).
/** @requires safeInteger(k) && 0 <= k && k < xs.length
 *  @requires forall i in xs: xs[i] === null || 1 <= xs[i].length */
export function headAt(xs: (number[] | null)[], k: number): string {
  const copy = xs.slice();
  copy[k] = [];
  const row = xs[k] ?? null;
  if (row === null) return "";
  return row[0]!.toFixed(0);
}
