// A merged generic interface: `"b"` is no key of `{ a: number }`.
interface I<T, K extends keyof T> {
  a: K;
}
interface I<T, K extends keyof T> {
  b: T;
}
export function f(x: keyof { z: I<{ a: number }, "b"> }): "z" {
  return x;
}
