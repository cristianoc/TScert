// A computed key naming a synthesised member through a property access.
export function f(x: keyof { z: import("@fixture/whole").ByPropertyKey }): "z" {
  return x;
}
