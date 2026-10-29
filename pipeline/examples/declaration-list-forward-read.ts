// A default of the first declarator's pattern reads the second declarator's
// binding, uninitialized while the default runs: the binding is early, a
// checked cell, so the read throws as JavaScript's does (under Node,
// `forward([])` throws a ReferenceError and `forward([2])` returns 3).
export function forward(xs: readonly number[]): Within<{ value: "any"; store: "grow" }, number> {
  const [a = b] = xs, b: number = 1;
  return a + b;
}
