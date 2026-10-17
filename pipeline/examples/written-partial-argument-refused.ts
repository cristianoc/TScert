// An argument the fragment reads no term for: `Partial`'s value names its
// key (`T[P]`), which the mapped-type reader refuses, so the application has
// no argument term to oblige.
type G<T, K extends keyof T> = K;
export function f(x: keyof { z: G<Partial<{ 0: number }>, 0> }): "z" {
  return x;
}
