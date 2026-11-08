// Code units read below a string's length: `text.charCodeAt(i)` at
// `0 <= i < text.length` is a safe integer in [0, 0xFFFF] by `charCodeAt`'s
// bounded signature, which a function requiring a safe integer accepts
// (pretext's `shouldBreakFast(pairs, lastLast, last, ch)` of code units).

/** @requires safeInteger(c) && 0 <= c && c <= 65535 */
function isSpace(c: number): boolean {
  return c === 0x20;
}

export function spaces(text: string): number {
  let n = 0;
  for (let i = 0; i < text.length; i++) {
    if (isSpace(text.charCodeAt(i))) n++;
  }
  return n;
}
