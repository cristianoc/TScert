// Bounds pattern P16, the unsafe neighbour of `bounds-pattern-lazy-cell-refused`:
// another function writes a shorter table into the cell (run under Node after
// `reset()`: `undefined` at `number`). A refined cell contract must be proved
// at every write of the cell.
let bmp: Uint16Array | null = null;

export function reset(): void {
  bmp = new Uint16Array(1);
}

/** @requires safeInteger(cp) && 0 <= cp && cp < 65536 */
export function bitsAt(cp: number): number {
  const table = (bmp ??= new Uint16Array(65536));
  return table[cp]!;
}
