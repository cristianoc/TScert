// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// measurement.ts#getKanaKerning, measurement.ts#readLetterSpacing.
// `Number.isNaN` tests a value without converting it and writes nothing: a
// Boolean.
export function spacing(x: number): number {
  return Number.isNaN(x) ? 0 : x;
}
