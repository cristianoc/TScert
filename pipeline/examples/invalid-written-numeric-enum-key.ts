// A numeric enum member's key is the member: `"0"` is no key of
// `{ [N.A]: number }`.
enum N {
  A,
}
type G<T, K extends keyof T> = K;
export function f(x: keyof { z: G<{ [N.A]: number }, "0"> }): "z" {
  return x;
}
