// A static getter beside an instance one: its own symbol, inferred, refused.
export function f(
  x: keyof { z: typeof import("@fixture/whole").StaticGetter },
): "z" {
  return x;
}
