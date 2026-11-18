// A copy keeps its receiver's holes: `map` at a callback that pops its
// receiver leaves holes, so its copy is no `readonly number[]` and is
// refused as `get`'s argument (run under Node: `at(xs, (x) => (xs.pop(),
// x), 1)` with `xs = [1, 2]` returns `undefined`).
/** @requires safeInteger(i) && 0 <= i && i < zs.length */
function get(zs: readonly number[], i: number): number {
  return zs[i]!;
}
export function at(xs: number[], f: (x: number) => number, i: number): number {
  const ys = xs.map((x) => f(x));
  if (!Number.isSafeInteger(i) || i < 0 || i >= ys.length) return 0;
  const zs = ys.slice();
  return get(zs, i);
}
