// A property assigned a binding: that binding's annotation
// keeps its bound.
export function f(
  x: keyof { z: typeof import("@fixture/lib").assigned.m },
): "z" {
  return x;
}
