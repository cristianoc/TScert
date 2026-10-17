// `new Set` of a string and of an array in one function: the overlay states
// the iterable overload at an array and at a string, each a construct
// signature of `Set`'s scheme, and `new` selects the one its argument meets.
export function letters(word: string, codes: number[]): number {
  const seen = new Set(word);
  const known = new Set<number>(codes);
  return (seen.has("a") ? 1 : 0) + (known.has(1) ? 1 : 0) + seen.size;
}
