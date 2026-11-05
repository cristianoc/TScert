// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// measurement.ts#getFontMeasurement.
// Refusal: gate: the global RangeError is declared in
// typescript/lib/lib.es5.d.ts (library), an origin no reviewed entry
// admits.
// `new RangeError(…)`: the global `RangeError` has no reviewed entry.
export function check(font: string): string {
  if (font === "") throw new RangeError("font must be a font string");
  return font;
}
