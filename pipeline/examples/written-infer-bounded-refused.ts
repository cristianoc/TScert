// `infer U` at a bounded position: TypeScript's implied constraint on `U`
// is not modelled, so `U` meets no bound.
interface Box<T extends string> {
  a: T;
}
type Inner<T> = T extends Box<infer U> ? U : never;
export function f(x: Inner<Box<"a">>): "a" {
  return x;
}
