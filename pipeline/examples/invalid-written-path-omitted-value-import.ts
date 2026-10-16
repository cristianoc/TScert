// A member of `omitted`, its type from its owner's annotation: that annotation is swept.
export function f(
  x: keyof { z: typeof import("@fixture/whole").omitted.a },
): "z" {
  return x;
}
