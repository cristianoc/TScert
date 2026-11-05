// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// measurement.ts#getFontMeasurement.
// `new RangeError(m)` at a string message constructs an error whose message
// is that string and whose name, inherited from `RangeError.prototype`, is
// `"RangeError"`. A throw of it is an outcome.
export function check(font: string): string {
  if (font === "") throw new RangeError("font must be a font string");
  return font;
}
export function made(message: string): string {
  const error = new RangeError(message);
  return `${error.name}: ${error.message}`;
}
