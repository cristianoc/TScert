// A class's unannotated static field: its arrow parameter's annotation
// keeps its bound.
export function f(x: keyof { z: typeof import("@fixture/lib").Fields.g }): "z" {
  return x;
}
