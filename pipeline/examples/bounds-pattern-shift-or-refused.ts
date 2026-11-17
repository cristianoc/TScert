// Bounds pattern P21: shift left and bitwise or, as pretext's getClass reads
// a generated class table: `index` has a block number for every 256 code
// points, below `blocks`, and `values` holds `blocks` blocks of 256 classes.
// Fact: (hi << 8) | (c & 0xff) = 256 * hi + (c & 0xff) < 256 * blocks, for
// 0 <= hi < blocks <= 4352 (0x1100, the 256-blocks up to U+10FFFF).
// Pretext: line-breaks.ts getClass (as second blocker, after P5, which gives
// index[c >> 8] < blocks).
// Gap: `<<` and `|` have no rule stating their result; `>>` and `&` have.
/** @requires safeInteger(blocks) && 0 <= blocks && blocks <= 4352 && values.length === 256 * blocks && safeInteger(hi) && 0 <= hi && hi < blocks && safeInteger(c) && 0 <= c && c < 1114112 */
export function badBits(
  values: Uint8Array,
  blocks: number,
  hi: number,
  c: number,
): number {
  return values[(hi << 8) | (c & 0xff)]!;
}
