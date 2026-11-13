// Bounds pattern P9, the supported neighbour of `bounds-pattern-product-refused`:
// a constant stride, `last * 28 + 27` in a view of 6244 elements.
// Pretext: line-breaks.ts getWebKitLineRules's rows.
/** @requires rows.length === 6244 && safeInteger(last) && 0 <= last && last < 223 */
export function goodStride(rows: Uint8Array, last: number): number {
  return rows[last * 28 + 27]!;
}
