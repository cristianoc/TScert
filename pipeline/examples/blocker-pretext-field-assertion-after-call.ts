// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// rich-inline.ts#createLine, rich-inline.ts#layoutNextRichInlineLineRange,
// rich-inline.ts#measureRichInlineStats,
// rich-inline.ts#walkRichInlineLineRanges.
// Refusal: reject: source expression obligation: no derivation of its cast
// claim.
// A non-null assertion of a nullable field after a call to a function that
// tested it, `if (fitsWhole(flow, w)) return flow.wholeWidth!`: what the
// called function tested is not known at the call.
type Flow = { wholeWidth: number | null };

function fitsWhole(flow: Flow, maxWidth: number): boolean {
  return flow.wholeWidth !== null && flow.wholeWidth <= maxWidth;
}

export function width(flow: Flow, maxWidth: number): number {
  if (fitsWhole(flow, maxWidth)) return flow.wholeWidth!;
  return maxWidth;
}
