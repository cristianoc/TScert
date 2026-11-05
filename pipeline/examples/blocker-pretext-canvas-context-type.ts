// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// measurement.ts#addMetrics, measurement.ts#addUpTo,
// measurement.ts#clearMeasurementCaches, measurement.ts#contextTakesFont,
// measurement.ts#createMeasureState, measurement.ts#getCanvasFont,
// measurement.ts#getContext, measurement.ts#getCorrectedSegmentWidth,
// measurement.ts#getEngineProfile, measurement.ts#getFollowingSpaceMetrics,
// measurement.ts#getFontSpaceKerning, measurement.ts#getHyphenText,
// measurement.ts#getLayoutEngine, measurement.ts#getSegmentMetrics,
// measurement.ts#getSpaceKerning, measurement.ts#getSpaceWidth,
// measurement.ts#getTextWidth, measurement.ts#getWholeRunContext,
// measurement.ts#hasFamily, measurement.ts#isCanvasWordLetter,
// measurement.ts#isLigature, measurement.ts#measureFitAdvances,
// measurement.ts#measureIn, measurement.ts#setLocaleLanguage,
// measurement.ts#takesNoSpaceKerning, measurement.ts#textMayContainEmoji,
// measurement.ts#zeros.
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
