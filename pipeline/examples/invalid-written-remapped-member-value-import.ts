// A key-remapped member the checker synthesises: its origin is swept.
export function f(
  x: keyof { z: typeof import("@fixture/whole").remapped.xy },
): "z" {
  return x;
}
