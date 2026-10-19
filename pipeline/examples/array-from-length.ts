// `Array.from` of a length record calls the callback with each index, the
// value read at `unknown`: a fresh dense array of the callback's results.
export function evens(n: number): number[] {
  return Array.from({ length: n }, (_, i) => i * 2);
}
