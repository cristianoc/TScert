// A read of an element inside a closure, at an index nothing bounds: under
// Node `f([], 0)` returns `undefined` where `number` is claimed. The refusal,
// of the closure's code, names the missing facts of the element read's
// precondition.
export function f(xs: number[], i: number): number {
  const g = (j: number): number => xs[j]!;
  return g(i);
}
