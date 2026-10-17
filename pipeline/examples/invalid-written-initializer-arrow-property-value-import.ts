// An object literal's arrow property, its type its initializer's: its parameter's annotation
// keeps its bound.
export function f(x: keyof { z: typeof import("@fixture/lib").arrows.m }): "z" {
  return x;
}
