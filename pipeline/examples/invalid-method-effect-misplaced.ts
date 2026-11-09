// `Modifies` at a parameter's type: it states a written signature's effect at
// its result annotation only.
export function f(x: Modifies<{}, number>): number {
  return x;
}
