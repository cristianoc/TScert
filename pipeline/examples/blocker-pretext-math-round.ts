// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// line-break.ts#getTabAdvance, measurement.ts#countLigaturesOnFirstLetter,
// measurement.ts#getCharacterSpaceKerning, measurement.ts#getEmojiGlyphs,
// measurement.ts#getFontKanaKerning, measurement.ts#measureKanaKerning,
// measurement.ts#sameInk.
// Refusal: gate: Math.round is not in the reviewed overlay of library
// globals: round(x: number): number;.
// `Math.round`, not in the reviewed overlay of library globals.
export function stop(advance: number): number {
  return Math.round(advance * 60);
}
