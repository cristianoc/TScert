// An extends type with `infer`: TypeScript narrows `T` to `S extends string`
// in the true branch, the reader adds no assumption, so `B<T>` meets no bound.
type B<T extends string> = T;
type F<T> = T extends infer S extends string ? B<T> : never;
export function f(x: F<"a">): "a" {
  return x;
}
