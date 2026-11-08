// A call with no length equality: `second([1], [])` reads `ys[0]`, which is
// `undefined`, as a `number` (run under Node: `undefined`).

/** @requires safeInteger(i) && 0 <= i && i < xs.length && xs.length === ys.length */
function at(xs: number[], ys: number[], i: number): number {
  return ys[i]!;
}

export function second(xs: number[], ys: number[]): number {
  if (xs.length > 0) return at(xs, ys, 0);
  return 0;
}
