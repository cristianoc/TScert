// Unsafe neighbour of `merge-array-length-alias`: the modified branch shrinks
// `ys` to an empty array, so `ys[i]` reads `undefined` at `number` and
// `ys[i]! + 1` returns `NaN` under Node.

/** @requires safeInteger(i) && 0 <= i && i < xs.length */
export function badShrinkingMerge(
  xs: Dense<number[]>,
  cond: boolean,
  i: number,
): number {
  let ys: Dense<number[]> = xs;
  if (cond) {
    ys = [];
  }
  return ys[i]! + 1;
}
