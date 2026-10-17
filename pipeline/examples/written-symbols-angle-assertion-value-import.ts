// An angle-bracket assertion states its property's type.
export function f(
  x: keyof { z: typeof import("@fixture/whole").angled.m },
): "z" {
  return x;
}
