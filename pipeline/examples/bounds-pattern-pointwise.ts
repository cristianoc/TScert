// Bounds pattern P12, the supported neighbour of
// `bounds-pattern-pointwise-refused`: one array of arrays read below its
// element's own length.
// Pretext: line-break.ts's reads of breakableFitAdvances.
/** @requires safeInteger(i) && 0 <= i && i < fits.length */
export function good(fits: number[][], i: number): number {
  const advances = fits[i]!;
  let s = 0;
  for (let g = 0; g < advances.length; g++) s += advances[g]!;
  return s;
}
