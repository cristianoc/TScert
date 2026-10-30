// `Array.from` of a string steps the string's iterator, which yields each
// code point as a string: a fresh dense `string[]`, within the empty
// footprint, so a `map` callback calling it preserves its array. With a
// callback, it calls it with each code point and its index.
export function initial(part: string): string {
  return Array.from(part)[0].toUpperCase();
}

export function upper(words: readonly string[]): string[][] {
  return words.map((word) => Array.from(word).map((c) => c.toUpperCase()));
}

export function codes(word: string): number[] {
  return Array.from(word, (c, i) => (c.codePointAt(0) ?? 0) + i);
}
