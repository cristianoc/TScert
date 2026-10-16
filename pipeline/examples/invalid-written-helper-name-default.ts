// A source declaration spelled like the evaluator's generated name: the
// computed default is still `"a"`, which `0` does not meet.
type __TScertUse0 = number;
type G<T = { a: number }, K extends keyof T = keyof T> = K;
export function f(x: 0): G {
  return x;
}
