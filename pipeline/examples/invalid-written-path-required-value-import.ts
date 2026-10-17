// A member of `required`, its type from its owner's annotation: that annotation is swept.
export function f(
  x: keyof { z: typeof import("@fixture/whole").required.a },
): "z" {
  return x;
}
