// A property holding a call's result, whose function's body determines its
// result: a type inferred from code, refused.
export function f(
  x: keyof { y: typeof import("@fixture/lib").madeProperty.m },
): "y" {
  return x;
}
