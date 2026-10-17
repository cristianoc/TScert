// A set of a string's code points read as a `Set<number>`: the string form
// gives a `Set<string>`, and no form gives a `Set<number>` of a string.
export function digits(word: string): Set<number> {
  // @ts-expect-error: a string's elements are strings
  const s: Set<number> = new Set(word);
  return s;
}
