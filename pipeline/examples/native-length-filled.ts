// Pretext: measurement.ts#measureAnalysis and rich-inline.ts#prepareRichInline.
/** @requires safeInteger(n) && 0 < n && n <= 4294967295 */
export function filled(n: number): string {
  const xs = new Array<string>(n).fill("ok");
  return xs[n - 1]!.toUpperCase();
}
/** @requires safeInteger(n) && safeInteger(k) && 0 <= k && k < n && n <= 4294967295 */
export function lazy(n: number, k: number): string[] | null {
  let xs: string[] | null = null;
  (xs ??= new Array<string>(n).fill("ok"))[k] = "new";
  return xs;
}
