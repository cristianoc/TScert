// A word counter's step, `counts[word] = next(counts, word)`. A dictionary
// owns no `constructor` or `toString` until it counts them, so `counts[word]`
// at such a word finds the member every object inherits from
// `Object.prototype`, a function; `?? 0` keeps it and `+ 1` makes the count a
// string where the dictionary's type says a number.
export function next(counts: { [k: string]: number }, word: string): number {
  return (counts[word] ?? 0) + 1;
}
