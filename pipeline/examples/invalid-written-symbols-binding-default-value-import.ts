// A destructuring default supplies its binding's type: inferred, refused.
export function f(x: keyof { z: typeof import("@fixture/whole").dd }): "z" {
  return x;
}
