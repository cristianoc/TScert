// An empty array literal TypeScript types as a tuple, where a destructuring
// is its context: the union `string | []` the destructuring iterates holds
// that tuple's type, which the compiler's API panics writing: a tool failure
// located at the iterable.
export function first(s: string, c: boolean): string {
  const [ch] = c ? s : [];
  return ch ?? "";
}
