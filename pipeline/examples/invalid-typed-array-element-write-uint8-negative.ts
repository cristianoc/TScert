// A Uint8Array write of -1 stores its conversion, 255: the stored element is
// not the value the fact's body admits (run under Node: `wrapped([0, 0],
// Uint8Array.of(0), 0, -1)` stores 255 and reads `widths[256]`, `undefined`
// at `number`).

/** @requires safeInteger(k) && 0 <= k && k < items.length && safeInteger(v) && -1 <= v && v + 1 < widths.length
 * @requires forall i in items: safeInteger(items[i]) && 0 <= items[i] && items[i] + 1 < widths.length */
export function wrapped(widths: number[], items: Uint8Array, k: number, v: number): number {
  items[k] = v;
  return widths[items[k]! + 1]!;
}
