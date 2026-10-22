// An index other than `length - 1`: `length` itself is past the end of
// every array, and the read is `undefined`.
export function pastTheEnd(xs: readonly string[]): string {
  return xs[xs.length];
}
