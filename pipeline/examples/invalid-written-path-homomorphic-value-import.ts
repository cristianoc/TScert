// A member of `homomorphic`, its type from its owner's annotation: that annotation is swept.
export function f(
  x: keyof { z: typeof import("@fixture/whole").homomorphic.a },
): "z" {
  return x;
}
