// A signed shift right of a negative operand: for -128 <= d < 128,
// d >> 4 lies in [-8, 7], since 16 * (d >> 4) <= d <= 16 * (d >> 4) + 15,
// so (d >> 4) + 8 indexes a table of 16.
/** @requires table.length === 16 && safeInteger(d) && -128 <= d && d < 128 */
export function bucket(table: Uint8Array, d: number): number {
  return table[(d >> 4) + 8]!;
}
