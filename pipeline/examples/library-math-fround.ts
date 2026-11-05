// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// measurement.ts#getWebKitGenericFamilies.
// `Math.fround` of a number runs no conversion code and writes nothing: the
// nearest single-precision value, a number.
export function single(x: number): number {
  return Math.fround(x);
}
