// Pretext: measurement.ts#measureAnalysis and rich-inline.ts#prepareRichInline.
/** @requires safeInteger(n) && 0 < n && n <= 4294967295 */
export function filled(n: number): string {
  const xs = new Array<string>(n).fill("ok");
  return xs[n - 1]!.toUpperCase();
}
