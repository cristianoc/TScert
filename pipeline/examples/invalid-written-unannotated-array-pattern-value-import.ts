// A constant destructured from an array takes its type from its
// initializer, which no annotation states: refused.
export function f(x: keyof { z: typeof import("@fixture/lib").first }): "z" {
  return x;
}
