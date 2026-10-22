// TypeScript accepts this under --strict, but an empty array, or one whose
// last position is a hole, reads `undefined` at `length - 1`.
export function last(xs: readonly string[]): string {
  return xs[xs.length - 1];
}
