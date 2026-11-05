// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// measurement.ts#parseFontSize, measurement.ts#readWidthIn.
// `parseFloat` of a string, a primitive no conversion code runs on, writes
// nothing: a number, `NaN` where no prefix of the string spells one.
export function size(text: string): number {
  return parseFloat(text);
}
