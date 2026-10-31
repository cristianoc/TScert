// A Set's elements keep their type through an indexed read and an empty
// array fallback. The number return contract cannot hold for a string.
export function first(mentions: readonly Set<string>[], i: number): number {
  for (const name of mentions[i] ?? []) return name;
  return 0;
}
