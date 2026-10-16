// A default export object's computed key: its constant's annotation is
// swept, and `B<any>` there keeps its bound.
export function f(
  x: keyof { z: typeof import("@fixture/defaulted-key") },
): "z" {
  return x;
}
