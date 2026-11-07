// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// analysis.ts#getWebKitParagraphBreaks,
// analysis.ts#removeItemsSkippableSegmentBreaks,
// line-text.ts#getGraphemeEnds, rich-inline.ts#findSegmentSources,
// rich-inline.ts#getOpeningFit, rich-inline.ts#getPartWidth,
// rich-inline.ts#getSegmentIndex, rich-inline.ts#getSourceOffset,
// rich-inline.ts#narrowsLine.
// A non-null assertion of an array's element read inside its length,
// `widths[i]!` with `i < widths.length`: the test states that `i` is an index
// below the length of `widths`' store, which reaches the read; there
// `%ElementAt%`'s signature at an index below the length gives the element,
// and `number[]` is readable (a hole only where the element admits
// `undefined`), so the read is a number.
export function last(widths: number[]): number {
  let width = 0;
  for (let i = 0; i < widths.length; i++) width = widths[i]!;
  return width;
}
