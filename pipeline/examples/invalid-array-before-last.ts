// An index other than `length - 1`: `length - 2` is before the start of an
// array of length 1, and the read is `undefined`.
export function beforeLast(xs: readonly string[]): string {
  return xs[xs.length - 2];
}
