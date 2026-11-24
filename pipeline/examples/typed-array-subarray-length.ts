// `TypedArray.prototype.subarray(begin, end)` with `0 <= begin <= end <= view.length`
// has length `end - begin`.
/**
 * @requires safeInteger(n) && 0 <= n && n <= flags.length
 * @ensures result.length === n
 */
export function prefixFlags(flags: Uint8Array, n: number): Uint8Array {
  return flags.subarray(0, n);
}

/**
 * @requires safeInteger(n) && 0 <= n && n <= flags.length
 */
export function sumPrefix(flags: Uint8Array, n: number): number {
  const sliced = prefixFlags(flags, n);
  let total = 0;
  for (let i = 0; i < n; i++) total += sliced[i]!;
  return total;
}
