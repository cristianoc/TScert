// Operands of a commuting operator in either order: `0xff & c` is Mask's
// `c & 0xff`, so it lies in [0, 255] for any number c; `8 | x` is Or's
// `x | 8`, at most x + 8 < 16 for 0 <= x < 8.
/** @requires table.length === 256 */
export function maskedFirst(table: Uint8Array, c: number): number {
  return table[0xff & c]!;
}
/** @requires small.length === 16 && safeInteger(x) && 0 <= x && x < 8 */
export function oredFirst(small: Uint8Array, x: number): number {
  return small[8 | x]!;
}
