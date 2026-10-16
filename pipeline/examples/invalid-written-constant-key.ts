// A computed key `[n]` with `n: 0` is the number `0`: `"0"` is no key of it.
const n: 0 = 0;
type G<T, K extends keyof T> = K;
export function f(x: keyof { z: G<{ [n]: number }, "0"> }): "z" {
  return x;
}
