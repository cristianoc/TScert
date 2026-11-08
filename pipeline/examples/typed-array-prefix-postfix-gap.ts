// Pretext: a strict element bound excludes the final updated counter.
// Preserving this body across n++ needs separation from the element locations.
/** @requires widths.length <= 2147483647 */
export function buildPostfix(widths: number[]): number {
  const items = new Int32Array(widths.length);
  let n = 0;
  /** @invariant safeInteger(n) && 0 <= n && n <= items.length && items.length === widths.length && forall i < n of items: safeInteger(items[i]) && 0 <= items[i] && items[i] < widths.length */
  while (n < items.length) items[n++] = 0;
  let total = 0;
  for (let j = 0; j < n; j++) total += widths[items[j]!]!;
  return total;
}
