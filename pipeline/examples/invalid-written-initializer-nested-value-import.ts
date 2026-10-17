// A nested object literal's arrow property: its parameter's annotation
// keeps its bound.
export function f(
  x: keyof { z: typeof import("@fixture/lib").nested.inner.m },
): "z" {
  return x;
}
