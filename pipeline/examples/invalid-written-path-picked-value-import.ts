// A member of a `Pick`: its bound `K extends keyof T` is read at the
// arguments, and `B<any>` in its owner's annotation keeps its bound.
export function f(
  x: keyof { z: typeof import("@fixture/whole").picked.a },
): "z" {
  return x;
}
