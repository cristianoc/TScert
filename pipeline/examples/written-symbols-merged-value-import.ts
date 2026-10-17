// A class merged with an interface: one symbol, both declarations.
export function f(x: keyof { z: import("@fixture/whole").Merged }): "z" {
  return x;
}
