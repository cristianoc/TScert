// The same loop without `to <= xs.length`: the first disjunct bounds `i` by
// `to` alone, and the read past the length is `undefined` at `number` (run
// under Node: `sum([1], 0, 2, false)` is `NaN`).

/** @requires safeInteger(i) && 0 <= i && safeInteger(to) */
export function sum(xs: number[], i: number, to: number, more: boolean): number {
  let s = 0;
  while (i < to || (more && i < xs.length)) {
    s += xs[i]!;
    i++;
  }
  return s;
}
