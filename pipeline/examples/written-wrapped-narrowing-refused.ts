// A wrapped check type, `[T] extends [string]`: TypeScript narrows `T` in the
// true branch, the reader adds no assumption, so `B<T>` meets no bound.
type B<T extends string> = T;
type F<T> = [T] extends [string] ? B<T> : never;
export function f(x: F<"a">): "a" {
  return x;
}
