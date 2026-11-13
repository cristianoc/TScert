// Bounds pattern P12: a pointwise relation of two arrays.
// Fact: forall k < fits.length: extras[k] === null || extras[k].length === fits[k].length.
// Pretext: line-break.ts countPreparedLines, walkPreparedComplexLines,
// stepPreparedSimpleLineGeometry; rich-inline.ts getPartWidth; analysis.ts
// getWebKitParagraphBreaks (5 sites).
// Gap: a quantified clause reads one array's element; one relating two
// arrays at one index is refused at the source.
/** @requires safeInteger(i) && 0 <= i && i < fits.length && fits.length === extras.length
 * @requires forall k in fits: extras[k] === null || extras[k].length === fits[k].length */
export function bad(fits: number[][], extras: (number[] | null)[], i: number): number {
  const advances = fits[i]!;
  const e = extras[i]!;
  let s = 0;
  for (let g = 0; g < advances.length; g++) s += advances[g]! + (e === null ? 0 : e[g]!);
  return s;
}
