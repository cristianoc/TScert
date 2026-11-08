// A quantified fact over a typed array's elements stating `items[i] <=
// widths.length` bounds no read at an element: the read is at the length
// (run under Node: `widthAt([5], Int32Array.of(1), 0)` reads `widths[1]`,
// `undefined` at `number`).

/** @requires safeInteger(k) && 0 <= k && k < items.length
 * @requires forall i in items: safeInteger(items[i]) && 0 <= items[i] && items[i] <= widths.length */
export function widthAt(widths: number[], items: Int32Array, k: number): number {
  return widths[items[k]!]!;
}
