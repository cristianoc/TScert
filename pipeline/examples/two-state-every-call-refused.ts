// Rule Call for a two-state postcondition under a quantifier: `appendOne`
// keeps every element below the length `xs` had before the call, so after
// it every element below that length is still 1. A gap: the return check
// entails a quantified fact only from one naming the same bound, and the
// facts at `appendOne`'s return bound it by `xs.length`, equal to
// `old(xs.length) + 1`; so its postcondition is not established and the
// caller, which composes it into `n` bounding the quantifier, is refused.

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
