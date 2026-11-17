// A shift count outside [0, 31] is read modulo 32, as `>>` reads it:
// `c >> 40` is `c >> 8`, and `c >> -1` is `c >> 31`, which is 0 for
// 0 <= c < 2^31.
/** @requires index.length === 4352 && safeInteger(c) && 0 <= c && c < 1114112 */
export function blockOf(index: Uint16Array, c: number): number {
  return index[c >> 40]!;
}
/** @requires flags.length === 1 && safeInteger(c) && 0 <= c && c < 2147483648 */
export function signOf(flags: Uint8Array, c: number): number {
  return flags[c >> -1]!;
}
