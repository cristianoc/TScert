// A bound read at the arguments: `"b"` is no key of `{ a: number }`.
type Get<T, K extends keyof T> = T[K];
export function f(x: keyof { z: Get<{ a: number }, "b"> }): "z" {
  return x;
}
