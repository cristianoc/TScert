// Bounds pattern P14: length contracts of string and array natives.
// Fact: normalized.length <= text.length after `text.replace(/ +/g, " ")`.
// Pretext: gecko-line-breaks.ts getGeckoLineBreaks; line-breaks.ts
// getWebKitLineRules; han-kerning.ts getFontData (4 sites, and 33 of
// analysis.ts that depend on it).
// Gap: `replace` has no length contract, so the loop's entry edge lacks
// normalized.length <= text.length.
export function bad(text: string): number {
  const normalized = text.replace(/ +/g, " ");
  const breaks = new Uint8Array(text.length + 1);
  let s = 0;
  /** @invariant safeInteger(i) && 0 <= i && normalized.length <= text.length && breaks.length === text.length + 1 */
  for (let i = 0; i < normalized.length; i++) s += breaks[i]!;
  return s;
}
