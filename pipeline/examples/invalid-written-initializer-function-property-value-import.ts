// An object literal's function expression property: its parameter's annotation
// keeps its bound.
export function f(
  x: keyof { z: typeof import("@fixture/lib").functions.m },
): "z" {
  return x;
}
