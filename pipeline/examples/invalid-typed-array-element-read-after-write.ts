// A quantified fact over a typed array's elements across a write through
// another view of the same bytes: `subarray` views the receiver's buffer, so
// the write stores the length in `items` too, which the fact excluded, and
// the read after it is past the end (run under Node: `widthAfterWrite([5],
// Int32Array.of(0), 0)` stores `1` through `alias`, then reads `widths[1]`,
// `undefined` at `number`).

/** @requires safeInteger(k) && 0 <= k && k < items.length
 * @requires forall i in items: safeInteger(items[i]) && 0 <= items[i] && items[i] < widths.length */
export function widthAfterWrite(widths: number[], items: Int32Array, k: number): number {
  const alias = items.subarray(0);
  alias[k] = widths.length;
  return widths[items[k]!]!;
}
