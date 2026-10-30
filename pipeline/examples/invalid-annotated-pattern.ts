// An annotated pattern whose initializer does not meet its annotation: a
// read of a `number[]` past its end is `undefined`, which the tuple
// `[number, number]` does not admit (run under Node: `sum([])` binds `a`
// to `undefined`).
export function sum(xs: number[]): number {
  const [a, b]: [number, number] = [xs[0], xs[1]];
  return a + b;
}
