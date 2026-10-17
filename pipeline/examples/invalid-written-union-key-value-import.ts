// Members selected at a union of keys, each through a re-export.
export function f(
  x: (typeof import("@fixture/relay"))["selected" | "renamed"],
): "a" {
  return x;
}
