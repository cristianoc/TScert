// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// analysis.ts#alignToSource, gecko-line-breaks.ts#transformText,
// line-text.ts#getGraphemeEnds, measurement.ts#countEmojiGlyphs,
// measurement.ts#getExtraSpacings, measurement.ts#getSegmentFit,
// prepare.ts#getUnspacedGraphemes.
// `new Int32Array(n)`, through the global's reviewed entry: only
// constructed, at a length or an array of numbers.
export function ends(n: number): number {
  const out = new Int32Array(n);
  return out.length;
}
