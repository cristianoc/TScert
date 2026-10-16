// An overload set's public signature, and a getter's annotation for its
// paired setter, state their types.
export function f(
  x: keyof {
    y: typeof import("@fixture/whole").over;
    z: typeof import("@fixture/whole").Paired.prototype.m;
  },
): "y" | "z" {
  return x;
}
