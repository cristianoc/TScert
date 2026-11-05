// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// analysis.ts#getWebKitParagraphBreaks,
// analysis.ts#removeItemsSkippableSegmentBreaks,
// line-text.ts#getGraphemeEnds, rich-inline.ts#findSegmentSources,
// rich-inline.ts#getOpeningFit, rich-inline.ts#getPartWidth,
// rich-inline.ts#getSegmentIndex, rich-inline.ts#getSourceOffset,
// rich-inline.ts#narrowsLine.
// Refusal: reject: source expression obligation: no derivation of its cast
// claim.
// A non-null assertion of an array's element read inside its length,
// `widths[i]!` with `i < widths.length`: `number[]` is readable (every
// in-bounds read meets `number`, so it holds no hole), so the read is a
// number; the loop's bound is not used to rule out a read past the end.
export function last(widths: number[]): number {
  let width = 0;
  for (let i = 0; i < widths.length; i++) width = widths[i]!;
  return width;
}
