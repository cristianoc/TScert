// A class's unannotated field: its type inferred from its initializer,
// refused.
export function f(
  x: keyof { z: import("@fixture/lib").Unannotated["f"] },
): "z" {
  return x;
}
