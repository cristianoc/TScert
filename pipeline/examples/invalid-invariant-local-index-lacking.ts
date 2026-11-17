// A loop invariant on a local index that the body moves below 0: the back
// edge does not establish `0 <= i`. Under Node `sum([1, 2])` reads
// `xs[-1]` and returns `NaN` where every element read is claimed a number.
// The refusal names the invariant's fact the back edge lacks and the facts
// known there.
export function sum(xs: number[]): number {
  let i = 0;
  let s = 0;
  /** @invariant safeInteger(i) && 0 <= i */
  while (i < xs.length && i > -3) {
    s += xs[i]!;
    i = i - 1;
  }
  return s;
}
