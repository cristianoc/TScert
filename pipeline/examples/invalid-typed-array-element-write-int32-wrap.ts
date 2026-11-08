// An Int32Array write of a safe integer past 2^31 - 1 wraps: the stored
// element is no longer the value the fact's body admits (run under Node:
// `wrapped([1, 2], Int32Array.of(2147483647), 0, 2147483647, 2147483648)`
// stores -2147483648 and reads `widths[-4294967295]`, `undefined` at `number`).

/** @requires safeInteger(k) && 0 <= k && k < items.length && safeInteger(offset) && safeInteger(v) && offset <= v && v < offset + widths.length
 * @requires forall i in items: safeInteger(items[i]) && offset <= items[i] && items[i] < offset + widths.length */
export function wrapped(widths: number[], items: Int32Array, k: number, offset: number, v: number): number {
  items[k] = v;
  return widths[items[k]! - offset]!;
}
