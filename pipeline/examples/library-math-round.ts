// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// line-break.ts#getTabAdvance, measurement.ts#countLigaturesOnFirstLetter,
// measurement.ts#getCharacterSpaceKerning, measurement.ts#getEmojiGlyphs,
// measurement.ts#getFontKanaKerning, measurement.ts#measureKanaKerning,
// measurement.ts#sameInk.
// `Math.round` of a number runs no conversion code and writes nothing: the
// nearest integer, a number.
export function stop(advance: number): number {
  return Math.round(advance * 60);
}
