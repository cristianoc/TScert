// A precondition's fact over a stable field path (`to <= a.xs.length`),
// across calls before and in a loop: the loop head is proposed the path's
// fact, which the pass keeps across the calls through the stable field, and
// a callee's precondition over the same path reads it (pretext's
// `measureAnalysis`, its call of `getFollowingSpaceTail`).
export type A = { /** @stable */ readonly xs: number[] };

function note(n: number): number {
  return n + 1;
}

/** @requires safeInteger(i) && 0 <= i && i < to && safeInteger(to) && to <= a.xs.length */
function at(a: A, i: number, to: number): number {
  return a.xs[i]!;
}

/** @requires safeInteger(from) && 0 <= from && from <= to && safeInteger(to) && to <= a.xs.length */
export function sum(a: A, from: number, to: number): number {
  let s = note(0);
  for (let i = from; i < to; i++) s += at(a, i, to) + note(i);
  return s;
}
