// An application in a library type's argument keeps its bound, though
// TypeScript computes `"a"` for the `keyof`.
type B<T extends string> = T;
export function f(x: keyof Record<"a", B<number>>): "a" {
  return x;
}
