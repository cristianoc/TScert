// Bounds pattern P21: shift left and bitwise or.
// Fact: (hi << 8) | (c & 0xff) = 256 * hi + c mod 256 < 4352 * 256.
// Pretext: line-breaks.ts getClass (as second blocker, after P5).
// Gap: `<<` and `|` have no rule stating their result; `>>` and `&` have.
/** @requires safeInteger(hi) && 0 <= hi && hi < 4352 && values.length === 1114112 && safeInteger(c) && 0 <= c && c < 1114112 */
export function badBits(values: Uint8Array, hi: number, c: number): number {
  return values[(hi << 8) | (c & 0xff)]!;
}
