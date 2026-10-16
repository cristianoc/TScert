// An unannotated arrow constant: its parameter's annotation
// keeps its bound.
export function f(x: keyof { z: typeof import("@fixture/lib").arrow }): "z" {
  return x;
}
