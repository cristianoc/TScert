// A function returning its input under `Fresh<T>`, and a caller relying on
// the promise: were the statement read as written, `alias` would read `xs`
// and `ys` as two arrays, but they are one (run under Node: `xs[0]` is
// `undefined` after `ys.pop()`).
export function same(xs: number[]): Fresh<number[]> {
  return xs;
}

export function alias(xs: number[]): number {
  if (xs.length === 0) return 0;
  const ys = same(xs);
  ys.pop();
  return xs[0]!;
}
