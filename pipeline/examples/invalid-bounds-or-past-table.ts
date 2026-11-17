// A bitwise or bounded by the sum of its operands, past a table of 256:
// (1 << 8) | 0 is 256, and table[256] is undefined.
// Or states y <= x + x'; with x = 256 * hi <= 256 and x' <= 255 that is
// y <= 511, which the read below 256 does not have.
/** @requires table.length === 256 && safeInteger(hi) && 0 <= hi && hi <= 1 && safeInteger(lo) && 0 <= lo && lo <= 255 */
export function ored(table: Uint8Array, hi: number, lo: number): number {
  return table[(hi << 8) | lo]!;
}
