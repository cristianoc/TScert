// A member of `readonlyBox`, its type from its owner's annotation: that annotation is swept.
export function f(
  x: keyof { z: typeof import("@fixture/whole").readonlyBox.a },
): "z" {
  return x;
}
