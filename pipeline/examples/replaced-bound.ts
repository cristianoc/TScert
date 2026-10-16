// Applications a reader replaces, each within its bounds: mapped keys, a
// library mapped type's key, a rest read through an alias (and a chain of
// them), a function type's rest, and applications under a computed type's
// binders that do not name them.
type Key<T extends string> = "a";
type B<T extends string> = T;
type Inner<T extends string> = [T];
type Outer<T extends string> = Inner<T>;
export function mapped(x: { [K in Key<"s">]: number }): number {
  return x.a;
}
export function record(x: Record<Key<"s">, number>): number {
  return x.a;
}
export function rest(...a: Inner<"s">): "s" {
  return a[0];
}
export function chain(...a: Outer<"s">): "s" {
  return a[0];
}
export function signature(g: (...a: Inner<"s">) => number): number {
  return g("s");
}
export function under(
  x: keyof { [K in "a"]: B<"s"> } | keyof { b: <U>() => B<"s"> },
): "a" | "b" {
  return x;
}
