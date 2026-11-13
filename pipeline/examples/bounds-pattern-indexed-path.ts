// Bounds pattern P17, the supported neighbour of
// `bounds-pattern-indexed-path-refused`: the selected element's length tested
// where it is read.
// Pretext: line-break.ts stepPreparedSimpleLineGeometry.
type Cursor = { segment: number; grapheme: number };

/** @requires safeInteger(c.segment) && 0 <= c.segment && c.segment < fits.length && safeInteger(c.grapheme) && 0 <= c.grapheme */
export function tested(fits: number[][], c: Cursor): number {
  const advances = fits[c.segment]!;
  return c.grapheme < advances.length ? advances[c.grapheme]! : 0;
}
