// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// analysis.ts#getWebKitParagraphBreaks, analysis.ts#mapSourceLineBreaks,
// gecko-line-breaks.ts#getBreakStates, graphemes.ts#parseGraphemeRules,
// rich-inline.ts#setEmptyObjectFacts.
// Refusal: gate: the global Uint8Array is declared in
// typescript/lib/lib.es5.d.ts (library), an origin no reviewed entry
// admits.
// `new Uint8Array(n)`: the global `Uint8Array` has no reviewed entry.
export function flags(n: number): number {
  const out = new Uint8Array(n);
  return out.length;
}
