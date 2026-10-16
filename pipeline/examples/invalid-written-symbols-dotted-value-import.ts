// A dotted namespace's inner namespace and its members: swept.
export function f(x: keyof { z: typeof import("@fixture/whole").Dotted }): "z" {
  return x;
}
