// `test` of a global regex leaves its `lastIndex` where the match ended: the
// callback writes the regex it captures, a location holding a number, which
// changes no array: `map`'s result is dense. The write shows: the same line
// tests true, then false.
const word = /\w+/g;
export function marks(lines: string[]): boolean[] {
  return lines.map((l) => word.test(l));
}
