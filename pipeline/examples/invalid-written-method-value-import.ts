// An object literal's method selected by `typeof`: the method itself is
// swept, and `Bounded<any>` in its result keeps its bound.
export function f(
  x: keyof { z: typeof import("@fixture/lib").methods.m },
): "z" {
  return x;
}
