// The length is read before a `pop` shrinks the array: the index it gives is
// then past the end, and the read is `undefined`.
export function stale(xs: string[]): string {
  const n = xs.length;
  xs.pop();
  return xs[n - 1];
}
