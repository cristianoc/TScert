// Pretext: han-kerning.ts#getFontData, parallel arrays with the same length.
/** @requires safeInteger(k) && 0 <= k && k < xs.length */
export function mapped(xs: string[], k: number): string {
  const ys = xs.map((x) => x.toUpperCase());
  return ys[k]!.toUpperCase();
}
