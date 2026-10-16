// A member of a `Pick`: its application's bound `K extends keyof T` names a
// computation over a parameter, which has no term in the library's
// declaration, so the application is refused.
export function f(
  x: keyof { z: typeof import("@fixture/whole").picked.a },
): "z" {
  return x;
}
