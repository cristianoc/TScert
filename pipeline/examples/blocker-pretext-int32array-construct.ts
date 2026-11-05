// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// analysis.ts#alignToSource, gecko-line-breaks.ts#transformText,
// line-text.ts#getGraphemeEnds, measurement.ts#countEmojiGlyphs,
// measurement.ts#getExtraSpacings, measurement.ts#getSegmentFit,
// prepare.ts#getUnspacedGraphemes.
// Refusal: gate: the global Int32Array is declared in
// typescript/lib/lib.es5.d.ts (library), an origin no reviewed entry
// admits.
// `new Int32Array(n)`: the global `Int32Array` has no reviewed entry.
export function ends(n: number): number {
  const out = new Int32Array(n);
  return out.length;
}
