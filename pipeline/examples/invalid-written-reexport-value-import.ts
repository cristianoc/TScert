// A member selected through a re-export: the re-exported declaration is
// swept, and `Bounded<any>` there keeps its bound.
export function f(x: (typeof import("@fixture/relay"))["selected"]): "a" {
  return x;
}
