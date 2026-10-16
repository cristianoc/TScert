// An array's `length` read in a closed expression (an arrow's expression
// body, a condition's operands) is its store's, read as a number, as a
// statement reads it.
export function counts(): number {
  const f = (...rest: number[]): number => rest.length;
  const g = (xs: readonly string[]): number => xs.length;
  return f(1, 2) + g(["a"]);
}
export function nonEmpty(xs: number[], ys: readonly boolean[]): boolean {
  return xs.length === 2 && ys.length === 0;
}
