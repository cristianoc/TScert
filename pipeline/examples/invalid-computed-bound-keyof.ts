// A `keyof` alias keeps its bound: `{ b: string }` has no `a`.
type KeysOf<T extends { a: number }> = keyof T;
export function f(x: KeysOf<{ b: string }>): "b" {
  return x;
}
