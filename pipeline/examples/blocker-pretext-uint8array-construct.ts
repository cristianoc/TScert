// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// analysis.ts#getWebKitParagraphBreaks, analysis.ts#mapSourceLineBreaks,
// gecko-line-breaks.ts#getBreakStates, graphemes.ts#parseGraphemeRules,
// rich-inline.ts#setEmptyObjectFacts.
// `new Uint8Array(n)`, through the global's reviewed entry: only
// constructed, at a length or an array of numbers.
export function flags(n: number): number {
  const out = new Uint8Array(n);
  return out.length;
}
