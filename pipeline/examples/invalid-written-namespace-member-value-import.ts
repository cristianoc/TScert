// A member selected from a module's namespace: its declaration's
// annotation is swept, and `Bounded<any>` there keeps its bound.
export function f(x: (typeof import("@fixture/lib"))["selected"]): "a" {
  return x;
}
