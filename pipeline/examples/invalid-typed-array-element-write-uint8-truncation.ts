// A Uint8Array write takes the value modulo 256: the stored element is no
// longer the value the fact's body admits (run under Node: `truncated(
// new Array(100).fill(1), Uint8Array.of(200), 0, 260)` stores 4 and reads
// `widths[-196]`, `undefined` at `number`).

/** @requires safeInteger(k) && 0 <= k && k < items.length && safeInteger(v) && 200 <= v && v < 200 + widths.length
 * @requires forall i in items: safeInteger(items[i]) && 200 <= items[i] && items[i] < 200 + widths.length */
export function truncated(widths: number[], items: Uint8Array, k: number, v: number): number {
  items[k] = v;
  return widths[items[k]! - 200]!;
}
