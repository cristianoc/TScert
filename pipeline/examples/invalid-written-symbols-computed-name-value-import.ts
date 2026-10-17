// A computed member name's constant: its annotation, swept.
export function f(x: keyof { z: import("@fixture/whole").ComputedName }): "z" {
  return x;
}
