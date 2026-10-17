// An application under a mapped type's key keeps its bound, though
// TypeScript computes `"a"` for the `keyof` without it.
type B<T extends string> = T;
export function f(x: keyof { [K in "a"]: B<number> }): "a" {
  return x;
}
