// The array shrinks between the test and the read: `pop` changes the store's
// length, so the bound is gone (run under Node: `last([1])` returns
// `undefined` as a `number`).
export function last(xs: number[]): number {
  let i = 0;
  if (i < xs.length) {
    xs.pop();
    return xs[i]!;
  }
  return 0;
}
