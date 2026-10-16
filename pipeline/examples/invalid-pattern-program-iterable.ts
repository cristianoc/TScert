// A name an array pattern over an iterable binds past the iterator's end is
// `undefined`: the pattern's element is no number.
export function first(values: Iterable<number>): number {
  const [a] = values;
  return a;
}
