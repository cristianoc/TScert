// A static method beside an instance one: its own symbol, inferred, refused.
export function f(
  x: keyof { z: typeof import("@fixture/whole").StaticMethod },
): "z" {
  return x;
}
