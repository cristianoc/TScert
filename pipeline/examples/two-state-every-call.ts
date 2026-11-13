// Rule Call for a two-state postcondition under a quantifier: `appendOne`
// keeps every element below the length `xs` had before the call, so after
// it every element below that length is still 1. Its return establishes
// `forall i < old(xs.length) of xs: …` from the facts there, which bound the
// quantified fact by `xs.length`, at least `old(xs.length)` (prefix
// weakening); the caller composes the post into `n` bounding the quantifier.

/**
 * @requires 0 <= xs.length && xs.length <= 1000 && forall i in xs: safeInteger(xs[i]) && xs[i] === 1
 * @ensures forall i < old(xs.length) of xs: safeInteger(xs[i]) && xs[i] === 1
 */
function appendOne(xs: number[]): Modifies<{ values: "any"; stores: "grow" }, void> {
  xs.push(1);
}

/**
 * @requires safeInteger(n) && n === xs.length && n <= 1000 && forall i in xs: safeInteger(xs[i]) && xs[i] === 1
 * @requires safeInteger(k) && 0 <= k && k < n && bs.length === 2
 */
export function pickOne(xs: number[], n: number, k: number, bs: number[]): number {
  appendOne(xs);
  return bs[xs[k]!]!;
}
