// `Modifies` at an array's element type: no signature's result.
export function f(xs: Modifies<{}, number>[]): number {
  return xs.length;
}
