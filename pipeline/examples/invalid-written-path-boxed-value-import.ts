// A member of `boxed`, its type from its owner's annotation: that annotation is swept.
export function f(
  x: keyof { z: typeof import("@fixture/whole").boxed.a },
): "z" {
  return x;
}
