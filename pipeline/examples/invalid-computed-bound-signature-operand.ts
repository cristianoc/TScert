// An application in a generic signature keeps its bound, though TypeScript
// computes `"a"` for the `keyof` without it.
type B<T extends string> = T;
export function f(x: keyof { a: <U>() => B<number> }): "a" {
  return x;
}
