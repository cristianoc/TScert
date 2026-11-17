// The precondition of `safe-int-index.ts` over an index typed `number`:
// `0 <= i && i < xs.length` states no safe integer of `i`, whose type is
// not `SafeInt`, so the clause is refused (under Node `at([1, 2], 0.5)`
// passes the clause's comparisons and returns `undefined`).

/** @requires 0 <= i && i < xs.length */
function at(xs: number[], i: number): number {
  return xs[i]!;
}

export function first(xs: number[], i: number): number {
  if (0 <= i && i < xs.length) return at(xs, i);
  return 0;
}
