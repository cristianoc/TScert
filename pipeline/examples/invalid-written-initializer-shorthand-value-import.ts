// A shorthand property: the annotation of the binding supplying it
// keeps its bound.
export function f(
  x: keyof { z: typeof import("@fixture/lib").shorthand.shortValue },
): "z" {
  return x;
}
