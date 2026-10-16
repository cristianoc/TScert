// A constructor implementation's parameter property, under overloads: swept.
export function f(x: keyof { z: import("@fixture/whole").Ctor }): "z" {
  return x;
}
