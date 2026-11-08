// Pretext's Int32 index builders require the upper bound 2147483647.
/** @requires safeInteger(n) && 0 <= n && n < items.length && safeInteger(j)
 * @requires forall i < n of items: safeInteger(items[i]) && 0 <= items[i] */
export function invalidPrefix(widths: number[], items: Int32Array, n: number, j: number): number {
  const next = n + 1;
  items[n] = 2147483648;
  if (j < 0 || j >= next) return 0;
  const k = items[j]!;
  if (k >= widths.length) return 0;
  return widths[k]!;
}
