// A member of `intersected`, its type from its owner's annotation: that annotation is swept.
export function f(
  x: keyof { z: typeof import("@fixture/whole").intersected.a },
): "z" {
  return x;
}
