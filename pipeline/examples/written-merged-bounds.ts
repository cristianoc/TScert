// A merged generic interface: its parameters are one list across its
// declarations, the bound read at the arguments.
interface I<T, K extends keyof T> {
  a: K;
}
interface I<T, K extends keyof T> {
  b: T;
}
export function f(x: keyof { z: I<{ a: number }, "a"> }): "z" {
  return x;
}
