// A member of an annotated constant whose arrow has an expression body: the
// annotation is its type, and the body, code, is not swept.
export function f(
  x: keyof { z: typeof import("@fixture/lib").exprBody.m },
): "z" {
  return x;
}
