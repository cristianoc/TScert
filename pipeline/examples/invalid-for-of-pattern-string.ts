// An array pattern binding a `for...of` over strings: each element is a
// string, which the pattern steps by its iterator, a code point at a time,
// not by index; no rule reads a pattern over a host non-array iterable.
export function firsts(words: string[]): string {
  let out = "";
  for (const [first] of words) out += first ?? "";
  return out;
}
