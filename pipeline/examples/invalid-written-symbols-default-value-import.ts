// A module's default export expression: its assertion's type, swept.
export function f(x: keyof { z: typeof import("@fixture/defaulted") }): "z" {
  return x;
}
