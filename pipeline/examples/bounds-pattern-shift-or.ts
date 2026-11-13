// Bounds pattern P21, the supported neighbour of `bounds-pattern-shift-or-refused`:
// a shift right and a mask.
// Pretext: line-breaks.ts getClass.
/** @requires index.length === 4352 && safeInteger(c) && 0 <= c && c < 1114112 */
export function goodShift(index: Uint16Array, c: number): number {
  return index[c >> 8]! + (c & 0xff);
}
