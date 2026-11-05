// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// layout.ts#prepareInternal, layout.ts#prepareWithSegments,
// line-text.ts#buildLineTextFromRange, line-text.ts#buildRangeText,
// line-text.ts#getGraphemeStart, rich-inline.ts#createLine,
// rich-inline.ts#createOnlyItemLine, rich-inline.ts#fitsWhole,
// rich-inline.ts#getHyphenRooms,
// rich-inline.ts#getInternalPreparedRichInline,
// rich-inline.ts#getOpeningFit, rich-inline.ts#getPartWidth,
// rich-inline.ts#getSegmentIndex, rich-inline.ts#getSourceOffset,
// rich-inline.ts#getSourceUnits, rich-inline.ts#isSoftHyphenSegment,
// rich-inline.ts#layoutNextRichInlineLineRange,
// rich-inline.ts#materializeRichInlineLineRange,
// rich-inline.ts#measureRichInlineStats, rich-inline.ts#narrowsLine,
// rich-inline.ts#walkRichInlineLineRanges, rich-inline.ts#zeroList.
// Refusal: gate: type outside the fragment (ThisType) in
// typescript/lib/lib.es5.d.ts#Int32Array.
// An `Int32Array` in a signature: the library's declaration of `Int32Array`
// uses `ThisType`, a type outside the fragment. Pretext meets it in
// signatures and record types holding grapheme ends.
export function first(ends: Int32Array): number {
  return ends.length;
}
