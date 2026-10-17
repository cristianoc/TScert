// A conditional alias deciding a default that names an earlier parameter:
// `U` is `T`'s argument, `{ a: number }`.
type Keep<T = { a: number }, U = T> = U extends unknown ? U : never;
export function f(x: Keep): number {
  return x.a;
}
