// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// measurement.ts#getWebKitGenericFamilies.
// Refusal: gate: Math.fround is not in the reviewed overlay of library
// globals: fround(x: number): number;.
// `Math.fround`, not in the reviewed overlay of library globals.
export function single(x: number): number {
  return Math.fround(x);
}
