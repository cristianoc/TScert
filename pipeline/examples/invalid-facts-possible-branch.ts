// The branch where `xs.length !== ys.length`, with no precondition relating
// the lengths: its facts hold where the lengths differ, and the edge into
// the loop head does not establish the quantified invariant. Under Node,
// `f([1], [], [5])` reads `xs[5]`, `undefined`, and returns `NaN`.

export function f(xs: number[], ys: number[], ends: number[]): number {
  if (xs.length !== ys.length) {
    let s = 0;
    /** @invariant safeInteger(k) && 0 <= k && forall i in ends: safeInteger(ends[i]) && 0 <= ends[i] && ends[i] < xs.length */
    for (let k = 0; k < ends.length; k++) s += xs[ends[k]!]!;
    return s;
  }
  return 0;
}
