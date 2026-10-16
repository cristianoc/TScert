// A member the checker synthesises from a mapped type: its origin, the
// owner's annotation, is swept, and `B<any>` there keeps its bound.
export function f(
  x: keyof { z: typeof import("@fixture/whole").mappedConstant.a },
): "z" {
  return x;
}
