// A member of a spread object: its owner's type is inferred, refused.
export function f(
  x: keyof { z: typeof import("@fixture/whole").spread.a },
): "z" {
  return x;
}
