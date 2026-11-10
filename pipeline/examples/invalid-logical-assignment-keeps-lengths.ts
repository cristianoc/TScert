// A logical assignment whose right side pops the array keeps no length
// fact: `t ??= (xs.pop(), 0)` empties `[5]` before the read, so `xs[mi]` is
// `undefined` (run under Node: `sum([5], 0, 1)` returns `NaN`).
/** @requires safeInteger(from) && safeInteger(to) && 0 <= from && from <= to && to <= xs.length */
export function sum(xs: number[], from: number, to: number): number {
  let s = 0;
  let t: number | null = null;
  for (let mi = from; mi < to; mi++) {
    t ??= (xs.pop(), 0);
    s += xs[mi]!;
  }
  return s + (t === null ? 0 : t);
}
