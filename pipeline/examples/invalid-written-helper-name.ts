// A source declaration spelled like the evaluator's generated name: the
// bound is still `keyof { a: number }`, which `0` does not meet.
type __TScertUse0 = number;
type G<T, K extends keyof T> = K;
export function f(x: keyof { z: G<{ a: number }, 0> }): "z" {
  return x;
}
