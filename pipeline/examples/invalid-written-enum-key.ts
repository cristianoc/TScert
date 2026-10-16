// An enum member's key is the member, not its value: `"a"` is no key of
// `{ [E.A]: number }`.
enum E {
  A = "a",
}
type G<T, K extends keyof T> = K;
export function f(x: keyof { z: G<{ [E.A]: number }, "a"> }): "z" {
  return x;
}
