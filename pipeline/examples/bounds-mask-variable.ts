// A mask held in a variable: x & mask lies in [0, mask] for any number x
// and 0 <= mask < 2^31, so it indexes a table of 256 for mask < 256.
/** @requires table.length === 256 && safeInteger(mask) && 0 <= mask && mask < 256 */
export function maskedBy(table: Uint8Array, x: number, mask: number): number {
  return table[x & mask]!;
}
