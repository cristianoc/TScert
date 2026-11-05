// `new Array<T>(n)` bound to a name before its `fill`: the holes are read
// first. TypeScript types `xs[0]` as `number`; under Node `first` is
// `undefined` and `toFixed` throws a TypeError. Only the construct written
// directly as the receiver of `fill(v)` is admitted.
export function firstFixed(n: number): string {
  const xs = new Array<number>(n);
  const first = xs[0];
  xs.fill(0);
  return first.toFixed(1);
}
