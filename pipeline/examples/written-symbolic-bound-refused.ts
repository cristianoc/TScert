// A bound naming another parameter, its argument a binder of the use site:
// `keyof T` is computed only at an instance.
type Get<T, K extends keyof T> = T[K];
export function f<T extends { a: number }>(x: keyof { z: Get<T, "a"> }): "z" {
  return x;
}
