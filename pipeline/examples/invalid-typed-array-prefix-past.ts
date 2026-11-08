// Pretext: graphemes.findGraphemeEnds and gecko-line-breaks.transformText
// extend a prefix of valid indices before consuming it.
/** @requires safeInteger(n) && 0 <= n && n < items.length && safeInteger(v) && 0 <= v && v < widths.length && v <= 2147483647 && safeInteger(j)
 * @requires forall i < n of items: safeInteger(items[i]) && 0 <= items[i] && items[i] < widths.length */
export function invalidPrefix(widths: number[], items: Int32Array, n: number, v: number, j: number): number {
  const next = n + 1;
  items[n + 1] = v;
  if (j < 0 || j >= next) return 0;
  return widths[items[j]!]!;
}
