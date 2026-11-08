// Pretext: graphemes.findGraphemeEnds and gecko-line-breaks.transformText
// extend a prefix of valid indices before consuming it.
/** @requires safeInteger(n) && 0 <= n && n < items.length && safeInteger(v) && 0 <= v && v < widths.length && v <= 2147483647 && safeInteger(j)
 * @requires forall i < n of items: safeInteger(items[i]) && 0 <= items[i] && items[i] < widths.length */
export function extendPrefix(widths: number[], items: Int32Array, n: number, v: number, j: number): number {
  const next = n + 1;
  items[n] = v;
  if (j < 0 || j >= next) return 0;
  return widths[items[j]!]!;
}

/** @requires widths.length <= 2147483647 */
export function buildPrefix(widths: number[]): number {
  const items = new Int32Array(widths.length);
  let n = 0;
  /** @invariant safeInteger(n) && 0 <= n && n <= items.length && n <= 2147483647 && items.length === widths.length && forall i < n of items: safeInteger(items[i]) && 0 <= items[i] && items[i] < widths.length */
  while (n < items.length) {
    const next = n + 1;
    items[n] = n;
    n = next;
  }
  let total = 0;
  for (let j = 0; j < n; j++) total += widths[items[j]!]!;
  return total;
}

export function readPrefixCursor(items: Int32Array): number {
  const size = items.length;
  let total = 0;
  let n = 0;
  /** @invariant safeInteger(n) && 0 <= n && n <= items.length */
  while (n < size) total += items[n++]!;
  return total;
}

/** @requires widths.length <= 2147483647 */
export function buildPostfixPrefix(widths: number[]): number {
  const size = widths.length;
  const items = new Int32Array(size);
  let n = 0;
  /** @invariant safeInteger(size) && safeInteger(n) && 0 <= n && n <= items.length && items.length === size && size === widths.length && forall i < n of items: safeInteger(items[i]) && 0 <= items[i] && items[i] <= size */
  while (n < items.length) items[n++] = 0;
  let total = 0;
  for (let j = 0; j < n; j++) {
    for (let k = items[j]!; k < widths.length; k++) total += widths[k]!;
  }
  return total;
}
