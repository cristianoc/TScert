// A member of an object rest binding: its owner's type is inferred, refused.
export function f(x: keyof { z: typeof import("@fixture/whole").rest.a }): "z" {
  return x;
}
