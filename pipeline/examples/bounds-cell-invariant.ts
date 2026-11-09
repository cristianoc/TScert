// Pretext normalizePreparedLineStart: a counter updated inside an expression, a slot.
/** @requires xs.length <= ys.length */
export function walk(xs: number[], ys: number[]): number {
  let j = 0;
  let sum = 0;
  /** @invariant safeInteger(i) && safeInteger(j) && 0 <= j && j <= i */
  for (let i = 0; i < xs.length; i++) sum += ys[j++]!;
  return sum;
}
