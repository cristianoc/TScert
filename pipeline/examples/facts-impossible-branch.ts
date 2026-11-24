// The branch where `xs.length !== ys.length` under the precondition
// `xs.length === ys.length`: once the two length reads are dropped, the
// facts on its edges contain a false constant and hold at no environment.
// Its edge into the loop head is never taken, and checks nothing: the
// quantified invariant, which nothing establishes, included.

/** @requires xs.length === ys.length */
export function f(xs: number[], ys: number[], ends: number[]): number {
  if (xs.length !== ys.length) {
    let s = 0;
    /** @invariant safeInteger(k) && 0 <= k && forall i in ends: safeInteger(ends[i]) && 0 <= ends[i] && ends[i] < xs.length */
    for (let k = 0; k < ends.length; k++) s += xs[ends[k]!]!;
    return s;
  }
  return 0;
}
