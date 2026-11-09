// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// prepare.ts#needsComplexTextPath, prepare.ts#getScriptFactsAt,
// prepare.ts#mayHoldCursive.
// A non-null assertion of `codePointAt(i)` with `i` a counter from 0 below
// the string's length: `codePointAt` gives `undefined` only at a position
// before the start or past the end, which the loop's test rules out
// (`codePointAt`'s bounded signature, ARITHMETIC.md, "Linear facts").
export function astral(text: string): number {
  let count = 0;
  for (let i = 0; i < text.length; i++) {
    if (text.codePointAt(i)! > 0xffff) count++;
  }
  return count;
}
