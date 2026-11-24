// Without `n <= flags.length`, `flags.subarray(0, n)` clamps to `flags.length`,
// so claiming `result.length === n` is unsound and reading `[n - 1]` returns undefined.
/**
 * @requires safeInteger(n) && 0 < n
 * @ensures result.length === n
 */
export function clampedPrefix(flags: Uint8Array, n: number): Uint8Array {
  return flags.subarray(0, n);
}

/**
 * @requires safeInteger(n) && 0 < n
 */
export function readClamped(flags: Uint8Array, n: number): number {
  const sliced = clampedPrefix(flags, n);
  return sliced[n - 1]! + 1;
}
