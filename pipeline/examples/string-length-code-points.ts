// Code points read below a string's length: `text.codePointAt(i)!` at
// `0 <= i < text.length` is a number by `codePointAt`'s bounded signature,
// the loop's test stating `i` below the string's length, which the read of
// `text.length` states equal to it (`string-length`). A code point past
// 0xFFFF is a surrogate pair's, so `i += c > 0xFFFF ? 2 : 1` stays within
// the length; a `@requires` over `text.length` bounds a helper's index, and
// a written `@invariant` a `do` loop's position.
// Stands for pretext's `needsComplexTextPath`, `mayHoldCursive`,
// `getScriptFactsAt` and `isEastAsianSegmentBreak`.

export function astral(text: string): number {
  let count = 0;
  for (let i = 0; i < text.length; i++) {
    if (text.codePointAt(i)! > 0xffff) count++;
  }
  return count;
}

export function codePoints(text: string): number {
  let count = 0;
  for (let i = 0; i < text.length;) {
    const c = text.codePointAt(i)!;
    i += c > 0xffff ? 2 : 1;
    count++;
  }
  return count;
}

/** @requires safeInteger(i) && 0 <= i && i < text.length */
function after(text: string, i: number): number {
  const c = text.codePointAt(i)!;
  const next = i + (c > 0xffff ? 2 : 1);
  return next < text.length ? text.codePointAt(next)! : -1;
}

export function second(text: string): number {
  return text.length > 0 ? after(text, 0) : -1;
}

// A read of the empty string's length, and of an astral one's.
export function lengths(): number {
  return "".length + "\u{1F600}".length;
}

function isSpace(c: number): boolean {
  return c === 0x20;
}

// A code point assigned in a `do` loop from a position bounded by a
// precondition and a test, under a written invariant over the string's
// length.
/** @requires safeInteger(end) && 0 <= end */
export function lastCodePoint(text: string, end: number): number {
  if (end >= text.length) return -1;
  let pos = end;
  let cp: number;
  /** @invariant safeInteger(pos) && 0 <= pos && pos < text.length */
  do {
    cp = text.codePointAt(pos)!;
    pos += cp > 0xffff ? 2 : 1;
  } while (isSpace(cp) && pos < text.length);
  return cp;
}
