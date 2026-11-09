// The safe-integer range of each value term the linear facts name
// (ARITHMETIC.md, "Linear facts", `valueRange`): a safe integer lies
// between -(2^53 - 1) and 2^53 - 1, so `i - 1` with `1 <= i` and `i + 1`
// with `i < n` are safe integers, and a loop from `i - 1` reads below the
// length.

/** @requires safeInteger(i) && 1 <= i */
export function sumFromBefore(xs: number[], i: number): number {
  let s = 0;
  for (let j = i - 1; j < xs.length; j++) s += xs[j]!;
  return s;
}

/** @requires safeInteger(i) && safeInteger(n) && 0 <= i && i < n */
export function nextBelow(xs: number[], i: number, n: number): number {
  const j = i + 1;
  return j < xs.length && j <= n ? xs[j]! : 0;
}
