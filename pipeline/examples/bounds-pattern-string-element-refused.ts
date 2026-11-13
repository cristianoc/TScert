// Bounds pattern P11: a string's element read below its length.
// Fact: 0 <= i < text.length, so `text[i]` is a string.
// Pretext: analysis.ts segmentAtLineBreaks (2 sites); line-breaks.ts
// getWebKitLineRules; measurement.ts measureKanaKerning (5 sites).
// Gap: no rule gives a string's element at an index below its length.
export function badElement(text: string): string {
  let out = "";
  for (let i = 0; i < text.length; i++) out = text[i]!;
  return out;
}
