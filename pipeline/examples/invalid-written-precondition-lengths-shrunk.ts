// A length equality the heap changed after its test: `ys.pop()` shortens
// `ys`, so `first([1], [2])` reads `ys[0]` of an empty array, `undefined` as a
// `number` (run under Node: `undefined`).

/** @requires safeInteger(i) && 0 <= i && i < xs.length && xs.length === ys.length */
function at(xs: number[], ys: number[], i: number): number {
  return ys[i]!;
}

export function first(xs: number[], ys: number[]): number {
  if (xs.length !== ys.length) throw new Error("lengths differ");
  ys.pop();
  if (xs.length > 0) return at(xs, ys, 0);
  return 0;
}
