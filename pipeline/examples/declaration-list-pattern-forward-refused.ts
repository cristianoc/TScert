// A default of the first declarator's pattern reads a binding the second
// declarator's pattern declares: a pattern's binding read where it may be
// uninitialized is refused (under Node, `forward([], [])` throws a
// ReferenceError).
export function forward(xs: readonly number[], ys: readonly number[]): number {
  const [a = b] = xs, [b = 0] = ys;
  return a + b;
}
