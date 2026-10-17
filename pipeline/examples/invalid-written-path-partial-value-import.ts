// A member of `partial`, its type from its owner's annotation: that annotation is swept.
export function f(
  x: keyof { z: typeof import("@fixture/whole").partial.a },
): "z" {
  return x;
}
