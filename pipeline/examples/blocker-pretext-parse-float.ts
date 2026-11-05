// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// measurement.ts#parseFontSize, measurement.ts#readWidthIn.
// Refusal: gate: parseFloat(…) is not in the reviewed overlay of library
// globals: declare function parseFloat(string: string): number;.
// `parseFloat`, not in the reviewed overlay of library globals.
export function size(text: string): number {
  return parseFloat(text);
}
