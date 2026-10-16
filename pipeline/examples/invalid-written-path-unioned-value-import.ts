// A member of `unioned`, its type from its owner's annotation: that annotation is swept.
export function f(
  x: keyof { z: typeof import("@fixture/whole").unioned.a },
): "z" {
  return x;
}
