// The copy of a bounded binder's value is not a value of the binder: it meets
// the bound's record, but a binder narrower than its bound may fix a field
// the copy replaces. At `B := { name: "a"; size: number }` (run under Node:
// `relabel({ name: "a", size: 1 }).name` is "x", outside `"a"`).
export function relabel<B extends { name: string; size: number }>(b: B): B {
  return { ...b, name: "x" };
}
