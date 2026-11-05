// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// analysis.ts#classifySegmentUnit, analysis.ts#mapSourceLineBreaks,
// analysis.ts#markItemStarts, gecko-line-breaks.ts#setupClusterBoundaries,
// graphemes.ts#parseGraphemeRules, line-text.ts#buildRangeText,
// line-text.ts#getGraphemeStart, rich-inline.ts#getHyphenRooms,
// rich-inline.ts#getSourceUnits, rich-inline.ts#isSoftHyphenSegment.
// Refusal: reject: source expression obligation: no derivation of its cast
// claim.
// A non-null assertion of a typed array's element read inside its length,
// `flags[i]!` with `i < flags.length`: the read's claim is `undefined |
// number`, and the index's bound is not used to rule `undefined` out. A
// typed array has no holes, so the read is a number.
export function total(flags: Uint8Array): number {
  let sum = 0;
  for (let i = 0; i < flags.length; i++) sum += flags[i]!;
  return sum;
}
