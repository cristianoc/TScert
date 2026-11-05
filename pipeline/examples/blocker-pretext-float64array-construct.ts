// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// measurement.ts#getFontKanaKerning.
// `new Float64Array(n)`, through the global's reviewed entry: only
// constructed, at a length or an array of numbers.
export function kerning(n: number): number {
  const out = new Float64Array(n);
  return out.length;
}
