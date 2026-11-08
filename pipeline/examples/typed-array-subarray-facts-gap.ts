// A quantified fact over a typed array does not transfer to a `subarray` of
// it (gecko-line-breaks.ts returns `orig.subarray(0, n)`): the model holds
// the subarray's elements as a store of its own, which no fact names. The
// program is safe (run under Node: `first([5, 6], Int32Array.of(1, 0))` is 6).

/** @requires forall i in items: safeInteger(items[i]) && 0 <= items[i] && items[i] < widths.length */
export function first(widths: number[], items: Int32Array): number {
  const head = items.subarray(0, 1);
  return head.length === 0 ? 0 : widths[head[0]!]!;
}
