// A conditional on `mi + 1 < to` before a nested loop: the merge after it
// runs to `mi = to` (the test `mi <= to`): the read after the
// nested loop reads past `ys`: `undefined.toFixed` throws (run under Node).
/** @requires safeInteger(from) && safeInteger(to) && 0 <= from && from <= to && to <= ys.length */
export function sumAfter(from: number, to: number, xs: number[], ys: number[]): number {
  let s = 0
  /** @invariant safeInteger(mi) && safeInteger(from) && safeInteger(to) && from <= mi && to <= ys.length */
  for (let mi = from; mi <= to; mi++) {
    const after = mi + 1 < to
    if (after) s += 1
    for (let k = 0; k < xs.length; k++) s += xs[k]!
    s += ys[mi]!.toFixed().length
  }
  return s
}
