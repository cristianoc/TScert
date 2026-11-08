// Element writes of a typed array that keep a quantified fact over its
// elements (PROGRAM-TYPING.md, "Quantified clauses"): an Int32Array write at a
// valid index of a safe integer an Int32Array holds unchanged (at most
// 2^31 - 1, which an array's length does not bound) sets that
// element alone, so the fact holds after it of every other index, and of the
// written one where the value meets the body (`every-write`): a write of a
// checked value, and a loop clamping every element, pretext's builders
// writing an index into a table of indices (line-breaks.ts, `whole[value] =
// count`).

/** @requires safeInteger(k) && 0 <= k && k < items.length && safeInteger(v) && 0 <= v && v < widths.length && v <= 2147483647 && safeInteger(j)
 * @requires forall i in items: safeInteger(items[i]) && 0 <= items[i] && items[i] < widths.length */
export function writeThenRead(widths: number[], items: Int32Array, k: number, v: number, j: number): number {
  items[k] = v;
  if (j < 0 || j >= items.length) return 0;
  return widths[items[j]!]! + widths[items[k]!]!;
}

/** @requires safeInteger(limit) && 0 <= limit && limit < widths.length && limit <= 2147483647
 * @requires forall i in items: safeInteger(items[i]) && 0 <= items[i] && items[i] < widths.length */
export function clampAll(widths: number[], items: Int32Array, limit: number): number {
  for (let i = 0; i < items.length; i++) {
    if (items[i]! > limit) items[i] = limit;
  }
  if (items.length > 0) return widths[items[0]!]!;
  return 0;
}
