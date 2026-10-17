// An element read a test that the same element is defined guards: the test
// is not carried to the second read, which passes `string | undefined` where
// `Set.has` takes a string.
export function firstKnown(xs: string[], known: Set<string>): boolean {
  return xs[0] !== undefined && known.has(xs[0]);
}
