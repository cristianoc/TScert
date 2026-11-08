// Reads bounded by a strict comparison of a safe integer with a number
// literal: its passing answer states `i = k`, its failing one `i ≠ k`, which
// with `0 <= i` gives `1 <= i` for `k = 0`.

/** @requires safeInteger(i) && 0 <= i && i <= xs.length */
export function previousOrZero(xs: number[], i: number): number {
  return i === 0 ? 0 : xs[i - 1]!;
}

/** @requires safeInteger(i) && 0 <= i && i <= xs.length */
export function previousIfNonzero(xs: number[], i: number): number {
  if (i !== 0) return xs[i - 1]!;
  return 0;
}

/** @requires safeInteger(i) && 0 <= i && i <= xs.length */
export function firstOrPreviousPositive(xs: number[], i: number): boolean {
  return i === 0 || xs[i - 1]! > 0;
}

/** @requires safeInteger(i) && 0 <= i && i < xs.length */
export function atThree(xs: number[], i: number): number {
  if (i === 3) return xs[i - 3]!;
  return 0;
}
