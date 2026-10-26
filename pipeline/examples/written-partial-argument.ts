// An argument whose term is a mapped type over `keyof`: `Partial<{ 0: number }>`
// is `{ 0?: number }`, whose key `0` meets `G`'s bound.
type G<T, K extends keyof T> = K;
export function f(x: keyof { z: G<Partial<{ 0: number }>, 0> }): "z" {
  return x;
}
