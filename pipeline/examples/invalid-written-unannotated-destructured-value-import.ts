// A constant destructured from an object takes its type from its
// initializer, which no annotation states: refused.
export function f(
  x: keyof { y: typeof import("@fixture/lib").destructured },
): "y" {
  return x;
}
