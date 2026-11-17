// Bounds pattern P21: a shift right, a mask, a shift left and a bitwise or,
// as pretext's getClass reads a generated class table: `index` has a block
// number for every 256 code points, below `blocks`, and `values` holds
// `blocks` blocks of 256 classes.
// Fact: c >> 8 <= 4351 < index.length, and
// (hi << 8) | (c & 0xff) <= 256 * hi + 255 < 256 * blocks, for
// 0 <= hi < blocks <= 4352 (0x1100, the 256-blocks up to U+10FFFF).
// Pretext: line-breaks.ts getClass.
/** @requires index.length === 4352 && safeInteger(c) && 0 <= c && c < 1114112 */
export function goodShift(index: Uint16Array, c: number): number {
  return index[c >> 8]! + (c & 0xff);
}
/** @requires safeInteger(blocks) && 0 <= blocks && blocks <= 4352 && values.length === 256 * blocks && safeInteger(hi) && 0 <= hi && hi < blocks && safeInteger(c) && 0 <= c && c < 1114112 */
export function classBits(
  values: Uint8Array,
  blocks: number,
  hi: number,
  c: number,
): number {
  return values[(hi << 8) | (c & 0xff)]!;
}
