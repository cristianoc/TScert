// A mask of any number: x & 255 lies in [0, 255] for a fractional, negative,
// large or NaN x, since & reads x through ToInt32.
/** @requires table.length === 256 */
export function masked(table: Uint8Array, x: number): number {
  return table[x & 0xff]!;
}
