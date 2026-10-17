// An interface merged from two parts: each part's applications name that
// part's parameter, bounded as declared.
type B<T extends string> = T;
interface I<T extends string> {
  a: T;
}
interface I<T extends string> {
  b: B<T>;
}
export function f(x: keyof I<"a">): "a" | "b" {
  return x;
}
