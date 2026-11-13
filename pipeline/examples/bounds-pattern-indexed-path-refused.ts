// Bounds pattern P17: an index into the element another index selects.
// Fact: c.grapheme < fits[c.segment].length.
// Pretext: line-break.ts stepPreparedSimpleLineGeometry; rich-inline.ts
// getPartWidth (3 sites).
// Gap: a clause's path is a variable followed by field names; a path step
// indexed by a term is refused at the source.
type Cursor = { segment: number; grapheme: number };

/** @requires safeInteger(c.segment) && 0 <= c.segment && c.segment < fits.length && safeInteger(c.grapheme) && 0 <= c.grapheme && c.grapheme < fits[c.segment].length */
export function at(fits: number[][], c: Cursor): number {
  const advances = fits[c.segment]!;
  return advances[c.grapheme]!;
}
