// An element write at an index no fact bounds below the length may append,
// so it keeps no upper bound of a length: `xs.length <= ys.length` is lost
// and `ys[n - 1]` may be out of bounds (run under Node: `last([], [], 0)`
// returns `undefined`).
/** @requires safeInteger(k) && 0 <= k */
export function last(xs: number[], ys: number[], k: number): number {
  if (xs.length > ys.length) return 0;
  if ((k & 0x7fffffff) !== k || k > xs.length) return 0;
  xs[k] = 1;
  const n = xs.length;
  if (n === 0) return 0;
  return ys[n - 1]!;
}
