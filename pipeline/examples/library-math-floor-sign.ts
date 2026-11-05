// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// line-break.ts#getTabAdvance (Math.floor), measurement.ts#readLetterSpacing
// and measurement.ts#getWebKitGenericFamilies (Math.sign).
// `Math.floor` and `Math.sign` of a number run no conversion code and write
// nothing: each a number.
export function tabStop(advance: number, width: number): number {
  return (Math.floor(advance / width) + 1) * width;
}
export function direction(x: number): number {
  return Math.sign(x);
}
