// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// measurement.ts#readWidthIn.
// Refusal: gate: getComputedStyle(…) is not in the reviewed overlay of
// library globals.
// The DOM's `getComputedStyle`, not in the reviewed overlay of library
// globals.
export function width(element: Element): string {
  return getComputedStyle(element).width;
}
