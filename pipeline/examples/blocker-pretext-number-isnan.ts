// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// measurement.ts#getKanaKerning, measurement.ts#readLetterSpacing.
// Refusal: gate: Number.isNaN is not in the reviewed overlay of library
// globals: isNaN(number: unknown): boolean;.
// `Number.isNaN`, not in the reviewed overlay of library globals.
export function spacing(x: number): number {
  return Number.isNaN(x) ? 0 : x;
}
