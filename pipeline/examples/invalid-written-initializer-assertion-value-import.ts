// An unannotated constant asserted to a type: the assertion's type
// keeps its bound.
export function f(x: keyof { z: typeof import("@fixture/lib").asserted }): "z" {
  return x;
}
