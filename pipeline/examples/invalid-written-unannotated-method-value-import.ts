// A class method whose body determines its result: a type inferred from
// code, refused.
export function f(x: keyof { z: import("@fixture/lib").Inferring["m"] }): "z" {
  return x;
}
