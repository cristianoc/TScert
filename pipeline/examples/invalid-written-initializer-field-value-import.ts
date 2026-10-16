// A class's unannotated instance field: its arrow parameter's annotation
// keeps its bound.
export function f(x: keyof { z: import("@fixture/lib").Fields["f"] }): "z" {
  return x;
}
