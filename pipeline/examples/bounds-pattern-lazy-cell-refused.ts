// Bounds pattern P16: a cache location initialized at its first use.
// Fact: bmp === null || bmp.length === 65536 at every entry.
// Pretext: line-breaks.ts hasProperty, shouldBreakFast,
// nextBreakablePosition; measurement.ts getKanaKerning (4 sites).
// Gap: the cell's contract is its type, `Uint16Array | null`, so its earlier
// contents have no length fact.
let bmp: Uint16Array | null = null;

/** @requires safeInteger(cp) && 0 <= cp && cp < 65536 */
export function bitsAt(cp: number): number {
  const table = (bmp ??= new Uint16Array(65536));
  return table[cp]!;
}
