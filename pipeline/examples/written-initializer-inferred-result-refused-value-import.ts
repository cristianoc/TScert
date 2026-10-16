// A method whose result type its body determines, in a declaration the
// client's type depends on: the types that body's code produces are not
// read, so the selection is refused.
export function f(
  x: keyof { z: typeof import("@fixture/lib").inferred.m },
): "z" {
  return x;
}
