// A member selected through a renamed re-export.
export function f(x: (typeof import("@fixture/relay"))["renamed"]): "a" {
  return x;
}
