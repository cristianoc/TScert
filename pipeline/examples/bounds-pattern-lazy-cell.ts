// Bounds pattern P16, the supported neighbour of
// `bounds-pattern-lazy-cell-refused`: the table allocated where it is read.
// Pretext: line-breaks.ts's lazily unpacked tables.
/** @requires safeInteger(cp) && 0 <= cp && cp < 65536 */
export function bitsFresh(cp: number): number {
  const table = new Uint16Array(65536);
  return table[cp]!;
}
