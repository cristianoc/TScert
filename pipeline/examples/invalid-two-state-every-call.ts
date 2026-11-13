// The unsafe neighbour of `two-state-every-call`: `bs` has one element, so
// the element 1 that `appendOne` keeps below the old length reads `bs` at 1,
// past its end.

/**
 * @requires 0 <= xs.length && xs.length <= 1000 && forall i in xs: safeInteger(xs[i]) && xs[i] === 1
 * @ensures forall i < old(xs.length) of xs: safeInteger(xs[i]) && xs[i] === 1
 */
function appendOne(xs: number[]): Modifies<{ values: "any"; stores: "grow" }, void> {
  xs.push(1);
}

/**
 * @requires safeInteger(n) && n === xs.length && n <= 1000 && forall i in xs: safeInteger(xs[i]) && xs[i] === 1
 * @requires safeInteger(k) && 0 <= k && k < n && bs.length === 1
 */
export function pickOne(xs: number[], n: number, k: number, bs: number[]): number {
  appendOne(xs);
  return bs[xs[k]!]!;
}
