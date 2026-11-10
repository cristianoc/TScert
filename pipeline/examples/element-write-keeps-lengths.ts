// An element write at an index no fact bounds below the length may append
// to `out`, and `out` may be `xs`; it leaves every store no shorter, so
// `to <= xs.length` holds after `out[j] = …` and each `xs[i]` is in bounds
// (pretext's chain-1 writes).
/** @requires safeInteger(to) && 0 <= to && to <= xs.length && safeInteger(at) && 0 <= at */
export function f(xs: number[], out: number[], to: number, at: number): number {
  let s = 0;
  /** @invariant safeInteger(i) && safeInteger(to) && safeInteger(j) && 0 <= i && to <= xs.length */
  for (let i = 0, j = at; i < to; i++, j++) {
    if ((j & 0x7fffffff) !== j || j > out.length) throw new RangeError("index");
    out[j] = xs[i]!;
    s += xs[i]!;
  }
  return s;
}
