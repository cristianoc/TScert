// A write of a value the fact's body excludes: the element written is the
// length, and the read at it is past the end (run under Node:
// `writeLength([5], Int32Array.of(0), 0)` reads `widths[1]`, `undefined` at
// `number`).

/** @requires safeInteger(k) && 0 <= k && k < items.length
 * @requires forall i in items: safeInteger(items[i]) && 0 <= items[i] && items[i] < widths.length */
export function writeLength(widths: number[], items: Int32Array, k: number): number {
  items[k] = widths.length;
  return widths[items[k]!]!;
}
