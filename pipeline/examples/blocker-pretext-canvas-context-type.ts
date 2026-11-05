// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// measurement.ts#addMetrics, measurement.ts#addUpTo,
// measurement.ts#clearMeasurementCaches, measurement.ts#contextTakesFont,
// measurement.ts#countEmojiGlyphs,
// measurement.ts#countLigaturesOnFirstLetter,
// measurement.ts#createMeasureState, measurement.ts#getCanvasFont,
// measurement.ts#getCharacterSpaceKerning, measurement.ts#getContext,
// measurement.ts#getCorrectedSegmentWidth, measurement.ts#getEmojiGlyphs,
// measurement.ts#getEngineProfile, measurement.ts#getExtraSpacings,
// measurement.ts#getFollowingSpaceMetrics,
// measurement.ts#getFontMeasurement, measurement.ts#getFontSpaceKerning,
// measurement.ts#getHyphenText, measurement.ts#getKanaKerning,
// measurement.ts#getLayoutEngine, measurement.ts#getSegmentFit,
// measurement.ts#getSegmentMetrics, measurement.ts#getSpaceKerning,
// measurement.ts#getSpaceWidth, measurement.ts#getTextWidth,
// measurement.ts#getWebKitGenericFamilies,
// measurement.ts#getWholeRunContext, measurement.ts#hasFamily,
// measurement.ts#isCanvasWordLetter, measurement.ts#isLigature,
// measurement.ts#measureFitAdvances, measurement.ts#measureIn,
// measurement.ts#measureKanaKerning, measurement.ts#parseFontSize,
// measurement.ts#readLetterSpacing, measurement.ts#sameInk,
// measurement.ts#setLocaleLanguage, measurement.ts#takesNoSpaceKerning,
// measurement.ts#textMayContainEmoji, measurement.ts#zeros.
// Refusal: gate: duplicate field name in a record in
// typescript/lib/lib.dom.d.ts#HTMLCanvasElement.
// A record type with a `CanvasRenderingContext2D |
// OffscreenCanvasRenderingContext2D` field: the DOM library's
// `HTMLCanvasElement`, reached from it, declares a field twice. Pretext
// meets it in its own type `MeasureState`.
export type State = {
  context: CanvasRenderingContext2D | OffscreenCanvasRenderingContext2D;
  font: string;
};
export function font(s: State): string {
  return s.font;
}
