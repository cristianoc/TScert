// An invariant with a false entry cannot justify the counter's out-of-bounds read.
/** @requires xs.length <= ys.length */
export function broken(xs: number[], ys: number[]): number {
  let j = 1;
  let sum = 0;
  /** @invariant safeInteger(i) && safeInteger(j) && 0 <= j && j <= i */
  for (let i = 0; i < xs.length; i++) sum += ys[j++]!;
  return sum;
}
