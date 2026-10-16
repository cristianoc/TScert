// A nested selection of synthesised members: the root's annotation states them.
export function f(
  x: keyof { z: typeof import("@fixture/whole").nest.a.b },
): "z" {
  return x;
}
