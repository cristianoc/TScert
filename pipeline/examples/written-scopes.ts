// Written applications under binders, each within its bound: a dependent
// bound, a shadowed outer binder, a mapped key, a generic signature's binder,
// a conditional's narrowing, and a defaulted conditional
// alias.
type B<T extends string> = T;
type F<T> = T extends string ? B<T> : never;
type Keep<T = { a: number }> = T extends unknown ? T : never;
export function dependent<T extends string, U extends T>(x: B<U>): number {
  return 1;
}
export function shadowed<T extends string, U extends T>(
  x: keyof { a: <T extends number>() => B<U> },
): "a" {
  return x;
}
export function mapped(x: keyof { [K in "a" | "b"]: B<K> }): "a" | "b" {
  return x;
}
export function signature(x: keyof { a: <U extends string>() => B<U> }): "a" {
  return x;
}
export function narrowed(x: F<"a">): "a" {
  return x;
}
export function defaulted(x: Keep): number {
  return x.a;
}
