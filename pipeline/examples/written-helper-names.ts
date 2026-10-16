// Source declarations spelled like the evaluator's generated names, beside
// applications it evaluates.
type __TScertUse0 = number;
type __TScertProbe0<T, K> = number;
type G<T, K extends keyof T> = K;
type H<T = { a: number }, K extends keyof T = keyof T> = K;
export function bound(x: keyof { z: G<{ a: number }, "a"> }): "z" {
  return x;
}
export function defaulted(x: "a"): H {
  return x;
}
export function named(x: __TScertUse0, y: __TScertProbe0<1, 2>): number {
  return x + y;
}
