// An arrow property of an unannotated object literal: its own annotations
// state its type, and its expression body, code, is not swept.
export function f(
  x: keyof { z: typeof import("@fixture/lib").arrowed.m },
): "z" {
  return x;
}
