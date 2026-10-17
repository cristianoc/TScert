// A bounded generic class merged with an empty interface: one symbol, its
// application within the bound.
export function f(x: keyof { z: import("@fixture/whole").Bounded<"a"> }): "z" {
  return x;
}
